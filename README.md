# What

Catalog of solutions to the Self-Referential Squares problem. For more info on the problem, see [A383673](https://oeis.org/A383673)

JSON format:  
"n": grid size  
"count": number of solutions  
"solutions": list of solutions

Two types of solution formats exist, each element of the "solutions" list is one of these types:  
- Object, containing key "grid":
 - 2D array of the values of the solution
- List, containing integers:
 - This is the first column of a solution, except the 2nd to last element which is the cell at Row 0, Column N-1

The latter can be uncompressed via application of the Sequential Property. 