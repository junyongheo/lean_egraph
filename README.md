# ~~First~~ Second(!!) implementation at E-Graphs in Lean4

Notes to myself:
  - Questions to answer, code to fix are marked "TODO:" 
  - One day things to do are marked "SOMEDAY:" (for me, not you)

Project Structure:

core: Contains the core files for e-graph operations
  - NaiveDefs.lean
    - Contains the E-Graph and Analysis definitions for the naïve case
  - Naive.lean
    - Contains the core e-graph functions, such as push, union, canonicalise...
  - ListAsMaps.lean
    - A basic map-like structure used for the e-class map and hashcons
  - UnionFind.lean
    - UnionFind implementation, uses a flat structure instead of a tree s.t. every nodep points directly to its canonical representative
  - Invariants.lean
    - Contains the theorems to prove and propositions needed for the e-graph. TODO: partition into more files?
  - rewrite.lean
    - Pattern, Rule implementations
    - EMatch, Instantiate, Rewrite functions
    - Comments somewhat cleaned up, but not fully
    - E-Matching is implemented as a very basic tree backtracking

tests: contains the testing framework and tests
  - tests.lean
    - helpers functions for tests
  - egraphtests.lean
    - tests the core operations of the e-graph
      - union, congruence, rebuilding ...
  - rewritetests.lean
    - WIP: pattern matching and rewrite tests


TODO: 
1. Generic-ise some of the testing infrastructure
3. Minor changes and ideas marked with "TODO" in comments
4. Cleanup code and comments to clarify decisions
6. Think of a less boring name than lean egraph