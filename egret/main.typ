#import "lib.typ" : *

#show: ams-article.with(
  title: [Generic E-Graph in Lean4],
  authors: (
    (
      name: "Junyong Heo",
    ),
  ),
  bibliography: bibliography("refs.bib"),
)

This report summarises the work done for the Large Research Project Computer Science (XM_0130). Some sections double up as documentation on how to run and extend the system.

#outline()

= Introduction

== Problem Statement

When transforming a given input through a series of rewrites or optimisations, we often run into the problem that the order in which the rewrites are performed has an effect on the final value. This is often referred to as the _phase ordering problem_, and stems from the fact that rewrites are inherently destructive; take the example _(a #sym.times 2) / 2_ . Multiplying by a factor of 2 can more efficiently be done through bit shifts, and thus we apply _ (a #sym.times 2) / 2 #sym.arrow (a #sym.angle.l.double 1) / 2) _. While the rewrite leads us to a more efficient operation, it fails to see the global optimum of _ (a #sym.times 2) / 2 #sym.arrow a #sym.times (2 / 2) #sym.arrow a _. Equality saturation uses an e-graph to maintain classes of equivalent terms, allowing for non-destructive rewrites to sidestep this issue @egg.

While there currently exists an implementation of equality saturation and e-graphs for Lean 4 (hereafter referred to as Lean) internal terms in Lean, there is not yet a generic equality saturation framework adaptable to different domains and languages. This project aims to bridge that gap by developing a generic e-graph library in Lean, as well as a framework for equality saturation over a user-defined language, with support for rewrite rules and extraction. 

As it is, the library is not fully formalised. The project serves as an exploratory introduction into the subject and to prepare a foundation for a long term goal of enabling formally verified optimisation and equational reasoning for domain specific languages.

== Contributions

Specifically, this project makes the following contributions.

- A Generic E-Graph framework in Lean parameterised over a user-defined language
  - E-graph core (E-Node, E-Class, and E-Graph operations)
  - Pattern matching and (conditional) rewriting
  - Extensible execution framework and equality saturation
  - E-class analysis and cost extraction
- Documentation and examples
- Performance comparisons vs egg (Rust) (TODO: )
- Some profiling of the code for bottlenecks (TODO: )

= Background

A very short background for completeness' purposes.
== Lean 4
Lean is an interactive theorem prover and functional programming language based on dependent type theory and inductive constructions. In addition to mathematics, Lean can be used to prove properties about programs. It's powerful metaprogramming capabilities make it useful for defining and working with domain specific languages. 

== E-Graph <egdef>
E-Graphs are a representation of terms and congruence relations of these terms @egg. More precisely, an e-graph uses a union-find data structure to maintain equivalence relations of e-classes, which themselves hold a set of equivalent e-nodes. Therefore, rather than storing a single expression, e-graphs make it possible to compactly store multiple equivalent expressions, making it suitable for equality saturation and rewriting based optimisations.

Willsey et al. define an e-graph as a tuple $(U,M,H)$ where:

- U: A union-find data structure over e-class ids.
- M: An e-class map that maps e-class ids to e-classes
- H: A hashcons map from e-nodes to e-class ids.

Details related to implementation will be elaborated in a further section.


= Design

In this section we detail some overarching design choices made. Specific design decisions of note may be elaborated more in the appropriate section.

== Simple vs Dependent Typing

In this project, we elected to implement the e-graph in a simply typed form over a dependently typed one. The main motivation is that the e-graph was planned with functionality in mind, and while dependent typing can help preserve invariants throughout, simple typing makes it easier to reason about the logic without getting drowned in implementation details. Furthermore, egg-style deferred rebuilding often results in invariants being temporarily broken, such as non-canonical references and a stale hashcons. Therefore, we elect to separate the proofs from the core functionality, while still allowing proving invariants in the form of separate theorems later. A core benefit is therefore more efficient execution through ease of merging e-classes, updating the union find, and allowing to stay closer to egg's algorithms.

== Stateful Computation
Instead of a fully functional structure, we thread the e-graph state through computations. This choice is again mostly motivated by the focus on practicality and execution.

== Genericity

To allow the e-graph to work for any user defined language, we generalise the structure and put the burden of proof and implementation on the user. No assumptions and simplification on the language are made, and as such the user is free to introduce rules and constructs as needed. Additionally, the e-graph can only represent syntactic equivalence and rewrite rules, and the proof of rewrite rules must be provided by the user.

To help on the semantic rewriting, analysis can be extended within reason. However, we also don't enforce invariants and thus nothing stops the user from defining an ill-formed analysis, as I learned from my own testing.

= Implementation
In this section, we discuss implementation details. The words _list_ and _array_ are used interchangeably to refer to a generic collection. The words _set_ and _map_ are used in the normal sense; _set_ is used where uniqueness of the elements is important and _map_ for collections where one value is indexed by the other.

== Language

While the e-graph is parameterised over a generic language #sym.alpha, we put constraints of DecidableEq and Hashable. Hashable is used in the hashcons, as well as throughout the implementation in the form of a hashmap. While boolean equality suffices for the implementation we currently have, decidable equality is was chosen to open up the possiblity of verifying details about the data structure later.

Furthermore, while every structure derives Repr for easier debugging and visualisation, it is not strictly required.

== E-Graph Core

The core e-graph data structure consists of the e-node, e-class, and e-graph structures, as well as the _ (U,M,H) _ triple mentioned in section @egdef. _EClassId_ is used as a synonym for _Nat_ for clarity. 

=== E-Node

An e-node consists of:
- _head_ of type #sym.alpha.
- List _args_ of type EClassId.

The head represents a (TODO: word) construct of the language, whether it be a primitive or an operator. For example, the term (2 + 3) of type MathLang will have '+' : MathLang as the head and the ids of the canonical e-classes that hold the operands 2 and 3 in args.

=== E-Class

At its core, an e-class is nothing more than a collection of syntactically equivalent e-nodes. In addition, we maintain a list of parents, to better preserve the invariants required by the e-graph, improve efficiency through hashconsing, and efficient bookkeeping with merges.

To allow for analysis, we also provide a _data_ field of type D that is extendable by the user.

=== E-Graph

The e-graph consists of:
- Union-find data structure over e-class ids.
- Map from e-class ids to e-classes
- Hashcons of e-nodes to e-class ids
as well as two additions,
- List of "dirty" e-classes
- Map from operators to e-class ids

The union-find represents equivalences between e-classes and provides a suitable framework to for querying and union. The e-class map bridges the e-class ids in the union-find and the actual e-classes.

The "dirty" list keeps track of classes that need rebuilding, allowing us to mark classes for the deferred batch rebuilding. The operator map, a minor optimisation to reduce the search space during pattern matching, will be discussed more in @opmap.

=== Operations

The two main operations exposed to the user are the _push_ and _union_ operations. The _push_ operation introduces a new e-node to the e-graph, and _union_ marks an equivalence relation between two nodes, modifying the e-graph appropriately.

== Rewriting

Rewriting consists of two main parts, pattern matching and rewriting.

=== Pattern Matching

Pattern matching consists of taking a pattern with variables and finding complete terms that fit the pattern. For example, if we try match the pattern _?x + 0 #sym.arrow ?x_, against terms in the graph, we might find _foo(a,b) + 0_ fits the pattern. 

Intuitively, we can view it in this way: if we think of the terms as a syntax tree, we first find a node whose operator matches that of the pattern we need. In our example above, we find an operator node with value '+'. Then we look at its children, of which one is a "hole" and the other is a constant 0. If we see that the right child matches 0, then we can store the subtree of the left child as a match for the "hole". This is illustrated in the not very beautiful illustration below.

#figure(
  grid(
    columns: 3,
    gutter: 0mm,
    image("unknown.png", width: 40%),
    image("foobar.png", width: 40%),
  ), caption: "Syntax tree visualisation for e-matching"
)

After a rule finishes matching, we end up with a dictionary that shows all terms in the e-graph that fit the hole. A dictionary for a pattern with multiple holes would therefore look like:

Dict := { (?x, ?y) => [(foo,bar), (23, 50)]}


=== Rewriting

Rewriting takes the dictionary created above to create syntactically equivalent expressions. Given a rewrite rule that says _ ?x + ?y => ?y + ?x _, we take a pair of terms from the dictionary above and rearrange them according to the rewrite. Therefore, _ foo + bar _ is rewritten into _ bar + foo _, and the appropriate node is added to the graph.

It's important to remember that as e-graphs work across a *class* of equivalent terms, both the dictionary and the rewrites work on e-class ids and not nodes. Therefore, a more appropriate representation would be _ (EClass 5) + (EClass 7) _ => _ (EClass 7) + (EClass 5) _. 

=== Conditional Rewriting

As a bonus, we implemented an extendable conditional rewriting framework. The user can define and pass function of type _ Dict #sym.arrow EGraphM Lang Analysis Bool _ which takes the dictionary created in the pattern matching step that evaluates the entries. While this is most useful in conjunction with analysis, for example only rewriting if the e-class represents a constant, the user may pass on any evaluator. 

=== (Operator Indexed) Pattern Matching <opmap>

A simplification made is the choice of pattern matching algorithm. The e-matching algorithm implemented in this project is a backtracking search across the entire e-graph. However, to somewhat reduce the search space, the e-graph maintains a map of operators to e-class ids. For example, over a calculus-based language, the operator-map (or opmap), keeps track of the ids of all e-classes that contain a differentiation term. When we try and match an differentiation rule, we only need to search the e-classes indexed by the opmap. However, this results in an non-uniform speedup across operators, as the benefits of the technique are most visible in sparsely used operators. In our example, matching an addition rule will likely show a much slower speedup compared to naïve matching than differentiation, as equivalent addition based terms can come from rewrites of many other operations. We will discuss further improvements to the pattern matching in a later section.

=== Equality Saturation

An equality saturation function is also provided. Similar to egg, we implement phase separation, dividing each iteration into a search phase and rewriting phase. An obvious benefit is that this provides better parallelisation, but it also reduces the dependence on rewrite rule application order and makes each iteration more predictable.

In addition to egg's Search #sym.arrow Apply #sym.arrow Rebuild, we rebuild the opmap (operator map) at the beginning of every iteration to keep the information in the map up to date, ensuring we don't miss any potential matches or waste effort on classes that have been canonicalised away.

The Equality Saturation (eqSat) function takes 1 mandatory argument, a list of rewrite rules to use. However, we can also stop the function early by providing either an iteration limit (default: limit := 10) or a node limit argument.

=== Extraction

We implement a simple bottom up extractor taken from Egg's Extraction Gym @extractiongym. The user can pass a custom cost function, so long as it takes #sym.alpha #sym.arrow Nat.

= Running the Code

== Defining Language and Rules

To define a language, first we must define the syntax.  An example is given for a basic Add/Mul language.

\
```
inductive AddMul where
| lit   : Nat → AddMul
| var   : String → AddMul
| add   : AddMul
| mul   : AddMul
deriving DecidableEq, Hashable, Repr

instance : ToString AddMul where
toString
| .lit n   => s!"{n}"
| .var s   => s
| .add     => "+"
| .mul     => "*"

instance Analysis : EGraph.Analysis AddMul Unit where
  make    _  _ := ()
  join    _  _ := ()
  modify  eg _ := eg

abbrev EGraphIO := EGraphGenericIO AddMul Unit

```
\

Syntax can be defined inductively as shown above. While a base analysis instance is defined, if one is required the above definition is portable.

A further EGraphGenericIO that takes a language and analysis is provided which wraps the EGraph around a state monad and the IO monad. As most runtime functions take this, we suggest using it.

To facilitate testing, we provide an extensible s-expr style parsing interface. 

```
instance : ParseExpr MathLang where
  parse sx :=
  match sx with
  | .atom s =>
    match s.toNat? with
    | some n => some (.const n, [])
    | none   => some (.sym   s, [])
  | .list (head :: args) =>
    match head with
    | .atom "+"    => some (.add,  args)
    | .atom "-"    => some (.sub,  args)
    ...
    | .atom "cos"  => some (.cos,  args)
    | _ => none
  | .list [] => none

```
\
We also find it useful to define functions to lift syntax into the Pattern class. While this does not force the arity of an operator, it does stop ill-formed rules from being parsed.

To help define rules, we have two functions, liftVar and liftTerm. liftTerm is used to shape our rule definitions, while liftVar is used to represent holes in the rules. 
\

```
def liftVar (s : String) : Pattern MathLang := Pattern.PatVar s
def liftTerm (h : MathLang) (args : List (Pattern MathLang)) : Pattern MathLang := Pattern.PatTerm h (Array.mk args)


def pAdd  (x y : Pattern AddMul ) := liftTerm (.add    ) [x, y]
def pMul  (x y : Pattern AddMul ) := liftTerm (.mul    ) [x, y]
...
def pLit (n : Int               ) := liftTerm (.lit   n) []
def pVar (s : String            ) := liftTerm (.var s  ) []
```

\ which allow us to define our rules as such

```
  r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
  r* pPow (?"x") (pConst 0) === (pConst 1) if (isNotZero "x"),
  r* pDiff {LHS} === {RHS} ifMultiple [
    (isNotZero "f"), (isNotZero "g")
  ]
```
\ By defining a few macros, we are able to define rules by following a format of "r\* {LHS} === {RHS}", followed by either "if {single condition}" or "ifMultiple { [list of conditions] }". Conditional functions may be defined as previously mentioned, with an example format
```
def isConst (var : String) : Dict Lang → EGraphM Lang Analysis Bool :=
  λ (dict) => (
    do
    ...
  )
```
\ The user may optionally define an Analysis instance by providing the make, join, and modify functions.

== Writing Tests and Programs

An example test looks like.

```
def math_diff_same : MathLangIO Unit := do
  let lhs ← parseTerm "(d x x)"
  let rhs ← push (.const 1)
  eqSat (rules := mathRules) (limit := 1)
  let _ ← checkEquivalent lhs rhs
```
\ We run the pushes with the general format of _ let id #sym.arrow.l parseTerm "term" _, where the return value is the e-class id of the pushed term.


There are a few ways to creates nodes. For an s-expression, we can use the parser we defined along with our language and use _parseTerm (+ 1 (+ 2 3))_, which recursively goes through the tree to push all the leaves (atoms) or lists needed to construct the expression. Note that an expression is a string and must be wrapped in parenthesis.



For individual nodes, we can use the _push_ macro and construct the node ourselves by passing the appropriate constructor. Similarly, a node with arguments can be pushed with _ push .add [x,y] _ where _x, y_ denote the e-class ids of the arguments of the node.


Therefore, these two sequences lead to the same e-graph state.

```
Sequence 1:
let one ← push (.const 1)
let two ← push (.const 2)
let thr ← push (.const 3)
let p12 ← push .add [one, two]
let p3a ← push .add [thr, p12]

Sequence 2:
let p3a ← parseTerm (+ 3 (+ 1 2))
```

The difference being that in the first sequence, we have access to the e-class ids of all the arguments, while in the second sequecne we only know the e-class id of the final term. However, thanks to the hashcons, it's perfectly possible to get the id of an individual node by pushing it again.

Finally, we also provide a checkEquivalent function that queries the e-graph whether two terms are syntactically equal.

At any time in the test, the user may call printEGraph to print the state of the e-graph.

An optional test_fn function is available in helpers.lean that mimics egg's test_fn! macro.



= Tests and Evaluation

== Correctness

== Performance

= Limitation and Improvements

== Limitations

backoff scheudler, better ematching, analysis is an absolute pain to work with and the semi-lattice thing is NOT maintained at all.

== Improvements

== Future Work

= Reflection

= Conclusion

