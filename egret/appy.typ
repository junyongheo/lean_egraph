

= Functions Available to the User <nicefuncs>

\

== Symbols and Abbreviations:
\ #sym.alpha is used to refer to the language defined by the user. There is a possibility this is changed to L in the future, but that should not affect functionality.

\ D is used to refer to the analysis data that can optionally be defined.

\ EClassId is an abbreviation for Nat 

\ 
== Useful Functions
\

\ *ENode:*

Definition:
\
#figure(
```
structure ENode (α : Type _ ) where
  head : α
  args : Array EClassId
deriving Hashable, DecidableEq, Repr
```
)

\ *EClass:*

Definition:
#figure(
```
structure EClass (α : Type _) (D : Type _) where
  nodes : Array (ENode α)
  parents : Array (ENode α × EClassId)
  data : D
deriving Repr
```
)

Constructors
#figure(
  ```
def EClass.empty [Inhabited D] {α : Type _} : EClass α D
def EClass.fromNode {α : Type _} (en : ENode α) (data : D) : EClass α D
  ```
)



\ *EGraph:*

Definition:
#figure(
```
structure EGraph (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
  uf    : Batteries.UnionFind
  ecmap : Std.HashMap EClassId (EClass α D)
  hcons : Std.HashMap (ENode α) EClassId
  dirty : Array EClassId
  opmap : Std.HashMap α (Array EClassId)
```
)

#figure(
  ```
abbrev EGraphM (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] :=
       StateM (EGraph α D)
  ```
) 

Rewrite: While the functionality is no longer used, it is theoretically possible to run a single rewrite by doing ``` rewrite "your rule here"  ```, or ``` rewrite (#sym.alpha := "your language") (D := "your analysis") (r := "your rule")```.

#figure(
```

```
)

\ *Analysis:*

Definition:
#figure(
```
class Analysis (α : Type _) (D : Type _)  [DecidableEq α][Hashable α] where
  make : (en : ENode α) → Array D → D
  join : D → D → D
  modify : EGraph α D → EClassId → EGraph α D
```
)

\ *Helpers:*

def lookupCanonicalEClassId (id : EClassId) : EGraphM α D <| EClassId

def findClass (en : ENode α) : EGraphM α D (Option EClassId)

\ 

\# Pushes the given node _en_ and runs Analysis.make

def pushRun [Analysis α D] (en : ENode α) : EGraphM α D EClassId

\# Unions the given classes and runs Analysis.join

def unionRun [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId

\# Rebuilds the e-graph and runs Analysis.modify

def rebuildRun [Analysis α D] : EGraphM α D (Unit)


\

\ \# Conditional Rewriting: See section @expls for an example of how to use CustomLookup
#figure(
  ```
inductive Condition (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
| Equal        : Pattern α → Pattern α           → Condition α D
| NotEqual     : Pattern α → Pattern α           → Condition α D
| CustomLookup : (Dict   α → EGraphM α D (Bool)) → Condition α D
```
)

\ \# Extraction:

abbrev cost := Nat

abbrev costFn α := α → cost


partial def extract (eg : EGraph α D) (fn : costFn α) : costMap α