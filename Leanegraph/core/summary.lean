import Batteries.Data.UnionFind

/-
  Summary of EGraph For Reasons...
-/
variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [Inhabited D]

namespace EGraph_S

/-
  EClassId is Nat
-/
abbrev EClassId := Nat

structure ENode (α : Type _ ) where
  head : α
  args : Array EClassId
deriving Hashable, DecidableEq, Repr

/-
  EClasses hold a Array of equivalent nodes and a Array of parents
  Performance is not an issue yet, Arrays instead of array for easier implementation
  TODO: switch to array (...eventually)
-/
structure EClass (α : Type _) (D : Type _) where
  nodes : Array (ENode α)
  parents : Array (ENode α × EClassId)
  data : D
deriving Repr

/-
  An e-graph is a tuple (U,M,H) of
    Union-find U - Equivalence relation over *e-class ids*
    E-class Map M - Map of *e-class ids to e-classes*
    Hashcons H - Map of *e-nodes to e-class ids*
-/
structure EGraph (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
  uf    : Batteries.UnionFind
  ecmap : Std.HashMap EClassId (EClass α D)
  hcons : Std.HashMap (ENode α) EClassId
  dirty : Array EClassId
  -- For performance reasons, add a mapping of all terms by operator
  opmap : Std.HashMap α (Array EClassId)


class Analysis (α : Type _) (D : Type _)  [DecidableEq α][Hashable α] where
  make : (en : ENode α) → Array D → D
  join : D → D → D
  modify : EGraph α D → EClassId → EGraph α D


/-
  State
-/
abbrev EGraphM (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] := StateM (EGraph α D)

/-
  ENode Operations
-/

def canonicalise (en : ENode α) : EGraphM α D (ENode α) := sorry

def updateParents (ecmap : Std.HashMap EClassId (EClass α D)) (en : ENode α) (eid : EClassId) : Std.HashMap EClassId (EClass α D) := sorry


/-
  EClass Operations
-/

def EClass.empty [Inhabited D] {α : Type _} : EClass α D := sorry

def EClass.fromNode {α : Type _} (en : ENode α) (data : D) : EClass α D := sorry

def EClass.merge (ec₁ ec₂ : EClass α D) (join : D → D → D) : EClass α D:= sorry


/-
  EGraph Operations
-/

def EGraph.size (eg : EGraph α D) : Nat := sorry

def EGraph.empty : EGraph α D:= sorry

def rebuildOpMap : EGraphM α D Unit := sorry

def repair (id : EClassId) (join : D → D → D) : EGraphM α D (Unit) := sorry

partial def rebuild (join : D → D → D) (modify : EGraph α D → EClassId → EGraph α D) : EGraphM α D (Unit) := sorry

def push {D : Type _} [Inhabited (EClass α D)] (en : ENode α) (make : ENode α → Array D → D): EGraphM α D (EClassId) := sorry

def union (id₁ id₂ : EClassId) (join : D → D → D) : EGraphM α D (EClassId) := sorry

def lookupCanonicalEClassId (id : EClassId) : EGraphM α D <| EClassId := sorry

def findClass (en : ENode α) : EGraphM α D (Option EClassId) := sorry

/-
  Misc Helpers
-/
def dedupArray [BEq α] [Hashable α] (myArray : Array α) : Array α := sorry
/-
  For Testing And Execution
  TODO: macros
-/

def pushRun [Analysis α D] (en : ENode α) : EGraphM α D EClassId := sorry

def unionRun [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId := sorry

def rebuildRun [Analysis α D] : EGraphM α D (Unit) := sorry

end EGraph_S



def testorem (n : Nat) (a : Array Nat) (l : List Nat) (h : l = a.toList) : (l ++ [n] = (a.push n).toList) :=
  by
    simp[h]
