//! Solver for Self-Referential Grids.
//!
//! Uses only constraints proven from CN1 + CN2' (paper by Jack Cats 2025):
//!
//!   CN1  — Latin square
//!   CN2' — Full domino property: g(g(r,c), g(r,c∔1)) = r  for all (r,c) 
//!        — g(g(r,c), g(r,c∔1) ∔ 1) = c  for all r, c
//!            (two applications of CN2' plus row-Latinness)
//!   S0   — g(a, a∔1) = n-1  for all a (pre-seeding)
//!   Theorem A — the last row is g(n-1, c) = c + k (dot arith) for a single 
//!          constant k. The outer k-loop enumerates it, pinning the 
//!          entire last row per branch. 
//!   Theorem B — the offset-2 diagonal shares the SAME k:  g(x, x∔2) = x - k
//!          for all x in Z_{n-1}.  Seeded per branch: n-1 more pinned cells.
//!   E2 — in row w < M:  g(w,c) = w∔k  <=>  g(w, c∔1) = w∔k∔2.
//!            Used in all four directions (main, converse, contrapositive,
//!            inverse), plus the corollary that neither symbol can sit in
//!            column M.
//!
//!
//! Output goes to data/proven_n{N:03}.json 
//!
//! ── Changing which rules run, and in what order ───────────────────────────
//! Every rule is a small named function. `pipeline()` near the bottom of the
//! "Rules" section lists them in three ordered groups:
//!   seeds      — run once per k-branch, before any propagation
//!   on_resolve — run, in order, every time a cell becomes a single symbol
//!   sweeps     — whole-board candidate passes, run (in order) whenever the
//!                resolution queue is empty, until nothing changes
//! Reorder or comment out entries there; nothing else needs to change.
//! Every rule is sound on its own, so any subset or order gives the same
//! solution set (only the speed differs).
//!
//! Usage:
//!   cargo run --release 
//!   cargo run --release -- 4 12   # range 4..=12

// ---------------------------------------------------------------------------
// Solver premise:
// Each cell of the grid is represented as an N bit mask of candidates, where
// a bit is set if the corresponding symbol hasn't been ruled out. The solver
// iteratively applies constraints, removing candidates until a contradiction
// is found (cell == 0) or all cells resolved (cell has a single bit set, and
// the grid is valid). Iteration is DFS. 
// 
// Workflow:
// 1. Pre-seeding: 
//      - S0 places N-1 in the cells g(a, a∔1) for all a < N-1, and
//        removes N-1 from all other cells.
//        - i.e. setting each aforementioned cell to 1<<(N-1)
// 2. k-seeding: 
//      - outer loop enumerates k in 0..N-2, and for each k:
//        - seed the last row g(N-1, j) = j + k for all j in 0..N-2
//        - seed the offset-2 diagonal g(x, x∔2) = x - k for all x in 0..N-2
//      - Note: the value k = g(N-1, 0) is used for some candidate reductions.
// 3. Iterate:
//      - Periodically* check if the grid is valid
//        - Validity check is expensive and does not often prune
//      - Find a cell with multiple candidates
//        - Unless none exist, then check if valid, record, and return
//      - Store the candidates, and for each candidate:
//        - Clone the grid with the candidate set.
//        - Apply reductions (CN1, CN2', E2) to prune the grid, and Iterate.
//
// Notes: 
//   - When a given cell is first resolved (becomes 1 bit set), it is
//     pushed onto a stack. Cells most recently resolved are expected to have
//     the most impact on other cells, so the reduction loop processes these
//     in LIFO order.  
//   - Reductions have some built-in contradiction detection, so if the grid
//     becomes invalid, the reduction loop returns false early.
//
// Reductions:
// 1. CN1: Latin square — remove the resolved symbol from all other cells in 
//      the same row and column.
// 2. CN2': Full domino property — if g(r,c) = s and g(r, c∔1) = t, then
//      g(s, t) = r.  If s or t is resolved, candidates might be removable
//      from some grid cells.
// 3. E2: for each row w, find c where g(w,c) = w∔k. The cell to the right
//      must be g(w, c∔1) = w∔k∔2. Also, if g(w, c∔1) cannot be w∔k∔2, 
//      then g(w,c) cannot be w∔k.  
// ---------------------------------------------------------------------------

use std::time::Instant;

const MAX_N: usize = 64; // u64 cell type
const DATA_DIR: &str = "data";

// ---------------------------------------------------------------------------
// Dot arithmetic
// ---------------------------------------------------------------------------

#[inline(always)] fn next_dot(a: usize, n: usize) -> usize {
    if a == n - 1 { n - 1 } else { (a + 1) % (n - 1) }
}

#[inline(always)] fn prev_dot(a: usize, n: usize) -> usize {
    if a == n - 1 { n - 1 } else { (a + n - 2) % (n - 1) }
}

// ---------------------------------------------------------------------------
// Board — uses u64 bitmasks, sized to actual N via runtime fields.
// Stack entries are (row, col) pairs of newly-resolved cells.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Board {
    n:          usize,
    m:          usize,          // n - 1
    k:          usize,             // seed constant for branch
    grid:       Vec<u64>,          // n*n cells, row-major
    stack:      Vec<(usize,usize)>,
    next_dot:   Vec<usize>,        // precomputed next_dot[i]
    prev_dot:   Vec<usize>,        // precomputed prev_dot[i]
    nbits:      u64,               // (1<<n)-1
}

impl Board {
    fn new(n: usize, k: usize) -> Self {
        assert!(n <= MAX_N, "N={n} exceeds MAX_N={MAX_N}");
        let nbits: u64 = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
        Board {
            n, m: n - 1, k,
            grid: vec![nbits; n * n],
            stack: Vec::new(),
            next_dot: (0..n).map(|i| next_dot(i, n)).collect(),
            prev_dot: (0..n).map(|i| prev_dot(i, n)).collect(),
            nbits,
        }
    }

    #[inline(always)] fn get(&self, r: usize, c: usize) -> u64 { self.grid[r * self.n + c] }
    #[inline(always)] fn set(&mut self, r: usize, c: usize, v: u64) { self.grid[r * self.n + c] = v; }

    /// The cell's symbol if it is resolved, else None.
    #[inline(always)] fn single(&self, r: usize, c: usize) -> Option<usize> {
        let v = self.get(r, c);
        if v.count_ones() == 1 { Some(v.trailing_zeros() as usize) } else { None }
    }

    /// Narrow cell (r,c) to `mask`. Returns false if the cell becomes empty.
    /// Pushes the cell onto the stack when it becomes a single symbol.
    /// 
    /// cell   | 111011 | 111011 | 111011
    /// mask   | 010101 | 000100 | 111111
    /// result | 010001 | 000000 | 111011
    /// return | true   | false  | true
    #[inline(always)] fn and_assign(&mut self, r: usize, c: usize, mask: u64) -> bool {
        let old = self.grid[r * self.n + c];
        let new = old & mask;
        if new == old { return true; }
        self.grid[r * self.n + c] = new;
        if new == 0 { return false; }
        if new.count_ones() == 1 { self.stack.push((r, c)); }
        true
    }

    /// Force cell (r,c) to hold `sym`.
    #[inline(always)] fn fix(&mut self, r: usize, c: usize, sym: usize) -> bool {
        self.and_assign(r, c, 1u64 << sym)
    }

    /// Rule out `sym` at cell (r,c).
    #[inline(always)] fn forbid(&mut self, r: usize, c: usize, sym: usize) -> bool {
        self.and_assign(r, c, !(1u64 << sym))
    }

    /// E2's two symbols for row w < M: (w∔k, w∔k∔2).
    #[inline(always)] fn e2_pair(&self, w: usize) -> (usize, usize) {
        let wk = (w + self.k) % self.m;
        (wk, (wk + 2) % self.m)
    }

    /// Extract the solved grid as a flat Vec<u8> (symbol per cell).
    fn extract(&self) -> Vec<u8> {
        self.grid.iter().map(|&v| v.trailing_zeros() as u8).collect()
    }
}

// ===========================================================================
// Rules
// ===========================================================================
//
// Three kinds, matching the three lists in `pipeline()`:
//   Seed     — fn(&mut Board) -> bool             (false = contradiction)
//   CellRule — fn(&mut Board, row, col, sym) -> bool
//              called when cell (row,col) has just resolved to `sym`
//   Sweep    — fn(&mut Board) -> Option<bool>     (None = contradiction,
//                                                  Some(changed))

type Seed     = fn(&mut Board) -> bool;
type CellRule = fn(&mut Board, usize, usize, usize) -> bool;
type Sweep    = fn(&mut Board) -> Option<bool>;

// ── Seeds ──────────────────────────────────────────────────────────────────

/// S0: g(a, a∔1) = M for every a.
fn seed_s0(b: &mut Board) -> bool {
    let m = b.m;
    (0..m).all(|a| { let c = b.next_dot[a]; b.fix(a, c, m) })
}

/// Theorem A: the last row is g(M, c) = c + k, and the corner g(M, M) = M.
fn seed_thm_a(b: &mut Board) -> bool {
    let (m, k) = (b.m, b.k);
    (0..m).all(|c| b.fix(m, c, (c + k) % m)) && b.fix(m, m, m)
}

/// Theorem B: the offset-2 diagonal is g(x, x∔2) = x - k.
fn seed_thm_b(b: &mut Board) -> bool {
    let (m, k) = (b.m, b.k);
    (0..m).all(|x| b.fix(x, (x + 2) % m, (x + m - k) % m))
}

/// E2 corollary: in row w < M, neither w∔k nor w∔k∔2 sits in column M.
///   w∔k at (w,M): CN2' at (w,M) gives g(w∔k, w∔k) = w, while Thm B gives
///                 g(w∔k, w∔k∔2) = w; row w∔k would hold w twice (m > 2).
///   w∔k∔2 at (w,M): w∔k is then at some ordinary column c0, and E2 puts a
///                 second copy of w∔k∔2 at c0∔1 != M.
fn seed_e2_column_m(b: &mut Board) -> bool {
    if b.m < 3 { return true; }
    let m = b.m;
    (0..m).all(|w| {
        let (wk, wk2) = b.e2_pair(w);
        b.forbid(w, m, wk) && b.forbid(w, m, wk2)
    })
}

// ── Cell rules (run when a cell resolves) ──────────────────────────────────

/// CN1: remove the symbol from the rest of its row and column.
fn rule_latin(b: &mut Board, row: usize, col: usize, sym: usize) -> bool {
    let mask = !(1u64 << sym);
    for i in 0..b.n {
        if i != col && !b.and_assign(row, i, mask) { return false; }
        if i != row && !b.and_assign(i, col, mask) { return false; }
            }
    true
        }

/// CN2' with (row,col) as the LEFT cell of the domino:
/// g(sym, g(row, col∔1)) = row.
fn rule_domino_right(b: &mut Board, row: usize, col: usize, sym: usize) -> bool {
    let next_col = b.next_dot[col];
    let right_val = b.get(row, next_col);
            if right_val.count_ones() == 1 {
                let right_sym = right_val.trailing_zeros() as usize;
        return b.and_assign(sym, right_sym, 1u64 << row);
    }
    // Prune options c for the right cell where g(sym, c) cannot be `row`.
                let mut opts = right_val;
                while opts != 0 {
        let bit = opts & opts.wrapping_neg();
        let c = bit.trailing_zeros() as usize;
        if b.get(sym, c) & (1u64 << row) == 0 && !b.and_assign(row, next_col, !bit) {
            return false;
                    }
                    opts &= !bit;
                }
    true
        }

/// CN2' with (row,col) as the RIGHT cell of the domino:
/// g(g(row, col∸1), sym) = row.
fn rule_domino_left(b: &mut Board, row: usize, col: usize, sym: usize) -> bool {
    let prev_col = b.prev_dot[col];
    let left_val = b.get(row, prev_col);
            if left_val.count_ones() == 1 {
                let left_sym = left_val.trailing_zeros() as usize;
        return b.and_assign(left_sym, sym, 1u64 << row);
    }
    // Prune options r' for the left cell where g(r', sym) cannot be `row`.
                let mut opts = left_val;
                while opts != 0 {
        let bit = opts & opts.wrapping_neg();
                    let r_prime = bit.trailing_zeros() as usize;
        if b.get(r_prime, sym) & (1u64 << row) == 0 && !b.and_assign(row, prev_col, !bit) {
            return false;
                    }
                    opts &= !bit;
                }
    true
}

/// E2, all four directions, triggered by a resolved cell (row < M, col < M):
///   main            (row,col) = w∔k    =>  (row,col∔1) = w∔k∔2
///   inverse         (row,col) != w∔k   =>  (row,col∔1) != w∔k∔2
///   converse        (row,col) = w∔k∔2  =>  (row,col∸1) = w∔k
///   contrapositive  (row,col) != w∔k∔2 =>  (row,col∸1) != w∔k
/// Eliminations that happen before any cell resolves are handled by
/// `sweep_e2_positions`.
fn rule_e2(b: &mut Board, row: usize, col: usize, sym: usize) -> bool {
    let m = b.m;
    if m < 3 || row >= m || col >= m { return true; }
    let (wk, wk2) = b.e2_pair(row);
    let (next, prev) = (b.next_dot[col], b.prev_dot[col]);
    let right_ok = if sym == wk  { b.fix(row, next, wk2) } else { b.forbid(row, next, wk2) };
    let left_ok  = if sym == wk2 { b.fix(row, prev, wk)  } else { b.forbid(row, prev, wk)  };
    right_ok && left_ok
}

/// g(g(r,c), g(r,c∔1) ∔ 1) = c for all r, c.
fn cn2_corollary(b: &mut Board, row: usize, col: usize, sym: usize) -> bool {
    // (row,col) as the left cell: u = sym, v = g(row, col∔1).
    let next_col = b.next_dot[col];
    if let Some(v) = b.single(row, next_col) {
        let target_col = b.next_dot[v];
        if !b.fix(sym, target_col, col) { return false; }
    }
    // (row,col) as the right cell: u = g(row, col∸1), v = sym.
    let prev_col = b.prev_dot[col];
    if let Some(u) = b.single(row, prev_col) {
        let target_col = b.next_dot[sym];
        if !b.fix(u, target_col, prev_col) { return false; }
    }
    true
}

// ── Sweeps (whole-board candidate passes) ──────────────────────────────────

/// E2 as a coupling of position sets. In row w < M let P1 be the ordinary
/// columns where w∔k is still possible and P2 those for w∔k∔2. E2 says
/// P2 = P1 ∔ 1 exactly, so each set is cut down to the shift of the other.
/// This applies all four directions at candidate level. When one column is
/// left, both symbols are placed (row-Latin: w∔k must appear somewhere, and
/// never in column M by `seed_e2_column_m`).
fn sweep_e2_positions(b: &mut Board) -> Option<bool> {
    let m = b.m;
    if m < 3 { return Some(false); }
    let full: u64 = (1u64 << m) - 1;
    let rot_fwd  = |p: u64| ((p << 1) | (p >> (m - 1))) & full; // {c∔1 : c ∈ p}
    let rot_back = |p: u64| ((p >> 1) | (p << (m - 1))) & full; // {c∸1 : c ∈ p}
    let mut changed = false;

    for w in 0..m {
        let (wk, wk2) = b.e2_pair(w);
        let (mut p1, mut p2) = (0u64, 0u64);
        for c in 0..m {
            let v = b.get(w, c);
            if v & (1u64 << wk)  != 0 { p1 |= 1u64 << c; }
            if v & (1u64 << wk2) != 0 { p2 |= 1u64 << c; }
        }
        let new1 = p1 & rot_back(p2);
        let new2 = p2 & rot_fwd(p1);
        if new1 == 0 || new2 == 0 { return None; }

        for c in 0..m {
            if (p1 & !new1) >> c & 1 == 1 {
                if !b.forbid(w, c, wk) { return None; }
                changed = true;
            }
            if (p2 & !new2) >> c & 1 == 1 {
                if !b.forbid(w, c, wk2) { return None; }
                changed = true;
            }
        }

        if new1.count_ones() == 1 {
            let c = new1.trailing_zeros() as usize;
            let nc = b.next_dot[c];
            let before = (b.get(w, c), b.get(w, nc));
            if !b.fix(w, c, wk) || !b.fix(w, nc, wk2) { return None; }
            if (b.get(w, c), b.get(w, nc)) != before { changed = true; }
        }
    }
    Some(changed)
}

// ── The pipeline: EDIT HERE to reorder or disable rules ────────────────────

struct Pipeline {
    seeds:      Vec<(&'static str, Seed)>,
    on_resolve: Vec<(&'static str, CellRule)>,
    sweeps:     Vec<(&'static str, Sweep)>,
}

fn pipeline() -> Pipeline {
    Pipeline {
        seeds: vec![
            ("S0",              seed_s0),
            ("Thm A",           seed_thm_a),
            ("Thm B",           seed_thm_b),
            ("E2 column M",     seed_e2_column_m),
        ],
        on_resolve: vec![ // The order of these has the most impact on speed.
                          // This appears to be close to optimal.
            ("CN1 latin",       rule_latin),
            ("CN2' corollary",  cn2_corollary),
            ("E2",              rule_e2),
            ("CN2' left",       rule_domino_left),
            ("CN2' right",      rule_domino_right),
        ],
        sweeps: vec![
            ("E2 positions",    sweep_e2_positions),
        ],
    }
}

/// Propagate to a fixpoint: drain the resolution stack through the cell
/// rules (in pipeline order); when it is empty, run the sweeps (in order);
/// repeat while anything changes. Returns false on contradiction.
fn reduce(board: &mut Board, pipe: &Pipeline) -> bool {
    loop {
        while let Some((row, col)) = board.stack.pop() {
            let sym = board.get(row, col).trailing_zeros() as usize;
            for (_, rule) in &pipe.on_resolve {
                if !rule(board, row, col, sym) { return false; }
            }
        }
        let mut progressed = false;
        for (_, sweep) in &pipe.sweeps {
            match sweep(board) {
                None => return false,
                Some(changed) => progressed |= changed,
            }
        }
        if !progressed && board.stack.is_empty() { return true; }
    }
}

// ---------------------------------------------------------------------------
// Validity check (used sparingly)
// ---------------------------------------------------------------------------

fn is_valid(board: &Board) -> bool {
    let n = board.n;
    // Each row and column must collectively cover all n symbols.
    for i in 0..n {
        let mut row_or = 0u64;
        let mut col_or = 0u64;
        for j in 0..n {
            row_or |= board.get(i, j);
            col_or |= board.get(j, i);
        }
        if row_or != board.nbits || col_or != board.nbits { return false; }
    }
    // Domino consistency: for resolved pairs, check the referral.
    // Checks according to CN2' (instead of just CN2).
    for r in 0..n {
        for c in 0..n {
            let rv = board.get(r, c);
            let cv = board.get(r, board.next_dot[c]);
            if rv.count_ones() == 1 && cv.count_ones() == 1 {
                let ri = rv.trailing_zeros() as usize;
                let ci = cv.trailing_zeros() as usize;
                if board.get(ri, ci) & (1u64 << r) == 0 { return false; }
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Recursive search
// ---------------------------------------------------------------------------

// Returns the first cell with multiple candidates
// Is apparently much slower than `least_unset`
fn first_unset(board: &Board) -> Option<(usize, usize)> {
    let n = board.n;
    for i in 0..n {
        for j in 0..n {
            if board.get(i, j).count_ones() > 1 { return Some((i, j)); }
        }
    }
    None
}

// Returns the first cell with the fewest candidates (but more than 1).
fn least_unset(board: &Board) -> Option<(usize, usize)> {
    let n = board.n;
    let threshold = 2;
    let mut best: Option<(usize, usize)> = None;
    let mut best_count = n + 1;
    for i in 0..n {
        for j in 0..n {
            let count = board.get(i, j).count_ones() as usize;
            if count > 1 && count < best_count {
                if count <= threshold { return Some((i, j)); }
                best_count = count;
                best = Some((i, j));
            }
        }
    }
    best
}

fn search(board: &mut Board, pipe: &Pipeline,
          solutions: &mut Vec<Vec<u8>>, check_valid: &mut usize) {
    // Periodic validity check (every 64 guesses)
    *check_valid += 1;
    if *check_valid % 64 == 0 && !is_valid(board) { return; }

    match least_unset(board) {
        None => {
            if is_valid(board) { solutions.push(board.extract()); }
        }
        Some((row, col)) => {
            let mut remaining = board.get(row, col);
            while remaining != 0 {
                let bit = remaining & remaining.wrapping_neg();
                remaining &= !bit;

                let mut child = board.clone();
                child.set(row, col, bit);
                child.stack.push((row, col));
                if reduce(&mut child, pipe) {
                    search(&mut child, pipe, solutions, check_valid);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Outer loop — One independent subproblem per k.
// ---------------------------------------------------------------------------

fn solve(n: usize, pipe: &Pipeline) -> Vec<Vec<u8>> {
    let mut all_solutions = Vec::new();
    for k in 0..n - 1 {
        let mut board = Board::new(n, k);
        if !pipe.seeds.iter().all(|(_, seed)| seed(&mut board)) { continue; }
        if !reduce(&mut board, pipe) { continue; }
        let mut check_valid = 0usize;
        search(&mut board, pipe, &mut all_solutions, &mut check_valid);
    }
    all_solutions
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

fn write_solutions(n: usize, solutions: &[Vec<u8>]) {
    std::fs::create_dir_all(DATA_DIR).expect("failed to create data dir");
    let path = format!("{DATA_DIR}/proven_n{n:03}.json");

    let mut json = format!("{{\n  \"n\": {n},\n  \"count\": {},\n  \"solutions\": [\n", solutions.len());
    for (si, sol) in solutions.iter().enumerate() {
        json.push_str("    {\n      \"grid\": [\n");
        for row in 0..n {
            let cells: Vec<String> = (0..n).map(|col| sol[row*n+col].to_string()).collect();
            let row_json = format!("        [{}]", cells.join(", "));
            if row + 1 < n { json.push_str(&format!("{row_json},\n")); }
            else            { json.push_str(&format!("{row_json}\n")); }
        }
        if si + 1 < solutions.len() { json.push_str("      ]\n    },\n"); }
        else                         { json.push_str("      ]\n    }\n"); }
    }
    json.push_str("  ]\n}\n");
    std::fs::write(&path, json).expect("failed to write solution file");
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (n_min, n_max) = match args.as_slice() {
        [a] => {
            let n: usize = a.parse().expect("expected integer N");
            (n, n)
        }
        [a, b] => {
            let lo: usize = a.parse().expect("expected integer");
            let hi: usize = b.parse().expect("expected integer");
            (lo, hi)
        }
        _ => (4, 16),
    };

    let pipe = pipeline();
    let names = |v: Vec<&str>| v.join(", ");
    println!("  seeds:      {}", names(pipe.seeds.iter().map(|r| r.0).collect()));
    println!("  on resolve: {}", names(pipe.on_resolve.iter().map(|r| r.0).collect()));
    println!("  sweeps:     {}", names(pipe.sweeps.iter().map(|r| r.0).collect()));
    println!("Range: N={n_min}..={n_max}");
    println!("All constraints proven from the rules.");
    println!();

    let total_start = Instant::now();
    let mut total = 0usize;

    for n in n_min..=n_max {
        if n < 3 { println!("N={n:3}: skipped (too small)"); continue; }
        let lap = Instant::now();
        let solutions = solve(n, &pipe);
        let ms = lap.elapsed().as_millis();
        let count = solutions.len();
        total += count;
        println!("N={n:3}: {count:4} solutions  ({ms}ms)");
        if count > 0 { write_solutions(n, &solutions); }
    }

    println!();
    println!("Total solutions: {total}");
    println!("Total time: {}ms", total_start.elapsed().as_millis());
}