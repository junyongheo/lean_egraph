# First implementation at E-Graphs in Lean4

Project Structure:

core: Contains the core files for e-graph operations
  - egraphs.lean
    - Over a generic language
    - Contains E-Node, E-Class, E-Graph implementations
    - Functions that operate on these implementations (push, merge, union)
    - Some stray comments and questions for myself
  - rewrite.lean
    - Pattern, Rule implementations
    - EMatch, Instantiate, Rewrite functions
    - Comments somewhat cleaned up, but not fully
    - E-Matching is implemented as a very basic tree backtracking
    - Attempted to optimise by keeping a map of operators to eclasses (see opmap field in egraph in egraph.lean)

tests: contains the testing framework and tests
  - tests.lean
    - helpers functions for tests
  - egraphtests.lean
    - tests the core operations of the e-graph
      - union, congruence, rebuilding ...
  - rewritetests.lean
    - WIP: pattern matching and rewrite tests


  - old_egraphs.lean
    - egraphs.lean but for a simpler language with only add/mul
    - Left as reference
    - (for me) left uncleaned for my own understanding
    - (for not me) may be helpful to understand what led me to a particular 

Simplifications
1. Uses Nat instead of Fin n for no dependent typing reasons. Lots of runtime checks with .get! and .find! operations that panic
1. Uses Lists instead of Array for easier implementation. Focusing initially on getting it running rather than performance

TODO: 
1. ~~Figure out best namespace practice and put egraphs in separate namespace~~
5. Finish writing test set
1. Organise code into different files
2. Change the lists to array
3. Minor changes and ideas marked with "TODO" in comments
4. Cleanup code and comments to clarify decisions
6. Cleanup functions by extracting functions from blocks of code when possible
6. Think of a less boring name than lean egraph