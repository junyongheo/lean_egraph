import Leanegraph.core

variable {α : Type _} [DecidableEq α] [BEq α][Hashable α] [Repr α]
variable {D : Type _} [Inhabited D]

namespace EGraph

-- TODO: is it better to abbrev cost := Nat and explicitly cost × ENode α or always bundle them together?
abbrev cost := Nat
abbrev costBundle α := (cost × ENode α)
abbrev costMap α := Std.HashMap EClassId (costBundle α)
-- List Nat and not List α because children are just Nats
-- on second thought we can make it EClassId to be clearer
-- TODO: Pass ENode α or α? Head or the entire node?
-- Ex) costFn α := ENode α → Nat
-- First thought: easier to pass separate for recursion purposes
-- costFn should implement: Base (no arg case) and yes arg case
-- abbrev costFn α := α → List EClassId → cost
abbrev costFn α := α → cost

-- Function that compares the cost of one enode with the current best
-- Bool is Changed (Terminate or Not)
def compareCosts (c : costBundle α) (cur : costBundle α) : (costBundle α) :=
  if c.fst < cur.fst then
    let new : costBundle α := (c.fst, c.snd)
    (new)
  else
    (cur)

def childCosts (eg : EGraph α D) (cm : costMap α) (children : List EClassId) : Option <| List Nat :=
  match children with
  | []                => some []
  | child :: children =>
    -- assume only canonical ids here DANGER: TODO: if id not found panic look here
    match cm.get? child with
    | some (cur, _en) =>
      -- [cur] ++ childCosts eg cm children
      -- cannot because we need to un-option it out first
      match childCosts eg cm children with
      | none => none
      | some list =>
        cur :: list
    | none   => none

def calcNodeCost (eg : EGraph α D) (cm : costMap α) (en : ENode α) (fn : costFn α) : Option <| costBundle α :=
  match (childCosts eg cm en.args) with
  | none => none
  | some val => ((fn en.head) + val.sum, en)

-- Gets lowest cost × node pairing for a certain eclass
def iterateNode (eg : EGraph α D) (ecls : EClass α D) (cm : costMap α) (fn : costFn α) : Option <| costBundle α :=
  ecls.nodes.foldl (init := none) (λ curMin nd =>
    let curCost := calcNodeCost eg cm nd fn
    match curCost with
    | some c =>
      match curMin with
      | none => (c)
      | some m => compareCosts c m-- if curCost.fst < m.fst then curCost else curMin
    | none =>
      match curMin with
      | none => none
      | some _ => curMin
    )
  -- lowestCost


partial def extract (eg : EGraph α D) (fn : costFn α) : costMap α :=

  let rec loop (cm : costMap α) : costMap α :=
    let (newMap, changed) : (costMap α × Bool) :=
      eg.ecmap.toList.foldl (init := (cm, false)) (λ (acc_cm, changed) (id, cls) =>
        let calcBest := iterateNode eg cls acc_cm fn
        let mapBest := acc_cm.get? id

        match calcBest, mapBest with
        | some new, some old =>
          if new.fst < old.fst then
            (acc_cm.insert id new, true)
          else
            (acc_cm, changed)
        | some new, none =>
          (acc_cm.insert id new, true)
        | _, _ =>
          (acc_cm, changed)
      )

    if changed then
      loop newMap
    else
      newMap

  loop Std.HashMap.emptyWithCapacity

end EGraph
