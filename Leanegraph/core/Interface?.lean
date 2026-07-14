import Leanegraph.core.SharedDefs
import Leanegraph.core.ListAsMaps
import Leanegraph.core.UnionFind
import Leanegraph.core.NaiveDefs
import Leanegraph.core.Naive
import Leanegraph.core.Rebuild

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

/-
  Exports for outside use
-/
abbrev EGraphM (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] := StateM (EGraph α D)

def lookupCanonicalEClassIdM (id : EClassId) : EGraphM α D EClassId := do
  return lookupCanonicalEClassId (← get) id

def pushM [Analysis α D] (en : ENode α) : EGraphM α D EClassId := do
  let (eg', id) := push (← get) en
  -- add analysis here
  discard <| set eg'
  return id

def unionM [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId := do
  let (eg', leader) := union (← get) id₁ id₂
  set eg'
  return leader

def rebuildM [Analysis α D] : EGraphM α D Unit := do
  set (rebuild (← get))
