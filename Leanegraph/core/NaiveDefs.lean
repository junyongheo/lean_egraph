import Leanegraph.core.SharedDefs
import Leanegraph.core.UnionFind
import Leanegraph.core.ListAsMaps

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]


/-
  In this file we define the basic structures: ENode, EClass, EGraph.
  We also provide the class definition for Analysis
    (TODO: why is this a class? does it matter? why?)

  and the default inhabited instances for each of the structures
-/

namespace Naive

structure ENode (α : Type _ ) where
  head : α
  args : List EClassId
deriving Hashable, DecidableEq, Repr
/-
inductive Term (α : Type _ ) where
| term : α → List (Term α) → Term α
deriving Repr
-/

structure Term (α : Type _) where
  head : α
  args : List (Term α)
deriving Repr
/-
  The parents list is a list of ENodes and their (TODO: canonical? only after repair) IDs
-/
structure EClass (α : Type _) (D : Type _) where
  nodes : List (ENode α)
  parents : List (ENode α × EClassId)
  data : D
deriving Repr

/-
  An e-graph is a tuple (U,M,H) of
    Union-find U - Equivalence relation over *e-class ids*
    E-class Map M - Map of *e-class ids to e-classes*
    Hashcons H - Map of *e-nodes to e-class ids*

  In the naïve version, we model a map by a list
  Helpers.lean defines operations and theorems that preserve map-like properties
  Operations on the "maps" should use the defined wrappers and not the built in list ops
-/
structure EGraph (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
  uf    : UF -- def UF := List <| EClassId × EClassId
  ecmap : ListMap EClassId (EClass α D) -- List <| EClassId × (EClass α D)
  hcons : ListMap (ENode α) EClassId-- List <| ENode α × EClassId
  dirty : List EClassId
  aldrt : List EClassId

/-
  Analysis
-/

class Analysis (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
  make : (en : ENode α) → List D → D
  join : D → D → D
  modify : EGraph α D → EClassId → EGraph α D



/---
  -
 ---/



/-
  Default Instances
-/

-- ENode
instance [Inhabited α] : Inhabited (ENode α) where
  default := {
    head := default
    args := []
  }

-- EClass
instance [Inhabited D] : Inhabited (EClass α D) where
  default := {
    nodes := []
    parents := []
    data := default
  }

-- Analysis
instance : Inhabited (Analysis α Unit) where
  default := {
    make    _  _ := (),
    join    _  _ := (),
    modify  eg _ := eg
  }

-- Analysis₂
-- To be honest I cannot remember why we needed two
-- TODO: figure this out I guess
-- This one is not an Inhabited instance?
instance : Analysis α Unit where
  make _ _ := ()
  join _ _ := ()
  modify eg _ := eg



end Naive
