import Leanegraph.core
import Leanegraph.framework

open EGraph

/-
  This test has some weird infrastructure, it moreso serves to show what is possible.
  Some of the e-graph internal functions are used that I was not planning on exposing to the user
-/

inductive Datalog where
| true_ : Datalog
| edge : Datalog
| path : Datalog
| int : Int → Datalog
deriving DecidableEq, Hashable, Repr

instance : ToString Datalog where
  toString
  | .true_ => "true"
  | .edge => "edge"
  | .path => "path"
  | .int i => s!"{i}"

instance : Analysis Datalog Unit where
  make    _ _ := ()
  join    _ _ := ()
  modify eg _ := eg

instance : ParseExpr Datalog where
  parse sx := match sx with
  | .atom "true" => some (.true_, [])
  | .atom s      => s.toInt?.map λ i => (.int i, [])
  | .list (.atom "edge" :: args) => some (.edge, args)
  | .list (.atom "path" :: args) => some (.path, args)
  | _ => none

def pEdge (a b : Pattern Datalog) := Pattern.PatTerm .edge #[a, b]
def pPath (a b : Pattern Datalog) := Pattern.PatTerm .path #[a, b]

abbrev DLIO := EGraphGenericIO Datalog Unit

-- Push true (hashcons handles duplicate pushes so e-graph not messed up)
-- and compare. canonicalise for good measure.
def isIdTrue (id : EClassId) : EGraphM Datalog Unit Bool := do
  let trueId ← pushRun {head := Datalog.true_, args := #[]}
  let c1 ← lookupCanonicalEClassId id
  let c2 ← lookupCanonicalEClassId trueId
  return c1 == c2

-- extends condition
-- matches pattern to construct the node
def isTrueNode (head : Datalog) (v1 v2 : String) : Dict Datalog → EGraphM Datalog Unit Bool :=
  λ subst => do
    let id1 := subst.get! v1
    let id2 := subst.get! v2

    -- but we DON'T push it because we don't know if this exists or not!
    let enode : ENode Datalog := { head := head, args := #[id1, id2] }

    -- consult the hashcons
    match (← get).hcons.get? enode with
    | some id => isIdTrue id
    | none => return false


def isTrueEdge (a b : String) := isTrueNode .edge a b

-- if (a, b) and (b, c) → (a, c)
-- if (a, b), find (b, c) and create (a, c)
def isTrueThenExtend (varfrom varto : String) : Dict Datalog → EGraphM Datalog Unit Bool :=
  λ subst => do
    let idfrom := subst.get! varfrom
    let idto := subst.get! varto

    -- is (a, b)?
    let pathIsTrue ← isTrueNode .path varfrom varto subst
    if not pathIsTrue then return false

    -- find all (b, c)
    let trueId ← pushRun {head := Datalog.true_, args := #[]}
    let trueClassId ← lookupCanonicalEClassId trueId
    let trueClass := ((← get).ecmap.get! trueClassId)

    let mut changed := false

    for n in trueClass.nodes do
      match n.head, n.args with
      | .edge, #[source, to] =>
          let canonsource ← lookupCanonicalEClassId source
          let canonto     ← lookupCanonicalEClassId idto

          if canonsource == canonto then
            let newPathId ← pushRun {head := .path, args := #[idfrom, to]}
            let _ ← unionRun newPathId trueId
            changed := true
      | _, _ => pure ()

    return changed

def datalogRules : List (Rule Datalog Unit) := [
  r* (pEdge (?"a") (?"b")) === (pPath (?"a") (?"b"))
     if (isTrueEdge "a" "b"),

  r* (pPath (?"a") (?"b")) === (pPath (?"a") (?"b"))
     if (isTrueThenExtend "a" "b")
]

def runDatalogTest : DLIO Unit := do
  let tr ← push (.true_)
  let e1 ← parseTerm "(edge 1 2)"
  let e2 ← parseTerm "(edge 2 3)"
  let e3 ← parseTerm "(edge 3 4)"

  -- Macro vs the unsugared function.
  let _ ← runLine <| unionRun e1 tr
  let _ ← union e2 tr
  let _ ← union e3 tr

  let t1 ← parseTerm "(path 1 4)"
  let t2 ← parseTerm "(path 4 1)"

  printEGraph
  eqSat (rules := datalogRules)
  printEGraph

  let _ ← checkEquivalent t1 tr
  let _ ← checkNonEquivalent t2 tr

#eval runTest runDatalogTest
