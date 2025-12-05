# First implementation at E-Graphs in Lean4

Files:
- egraphs.lean
  - (should be) Over a generic language
  - Contains E-Node, E-Class, E-Graph implementations
  - Functions that operate on these implementations (push, merge, union)
  - Some stray comments and questions for myself
- old_egraphs.lean
  - egraphs.lean but for a simpler language with only add/mul
  - left uncleaned for my own understanding
- rewrite.lean
  - WIP, only holds definition for pattern structure

Simplifications
1. Uses Nat instead of Fin n for no dependent typing reasons. Lots of runtime checks with .get! and .find! operations that panic
1. Uses Lists instead of Array for easier implementation. Focusing initially on getting it running rather than performance

TODO: 
1. Implement pattern matching and rewriting
1. Organise code into different files
1. Write a better README
2. Change the lists to array
3. Minor changes and ideas marked with "TODO" in comments
4. Cleanup code and comments to clarify decisions
5. Cleanup test set
6. Cleanup functions by extracting functions from blocks of code when possible
6. Think of a less boring name than lean egraph