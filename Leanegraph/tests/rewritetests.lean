import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers
import Leanegraph.languages.addmul

/-
  WIP
-/

open EGraph

variable {α : Type _} [DecidableEq α] [BEq α] [Hashable α]

/-
  Helpers for the AddMul Language
  TODO: rewrite them to be generic
-/

-- Lift var/term → Pattern
def pVar (s : String) : Pattern AddMul := Pattern.PatVar s
def pTerm (h : AddMul) (args : List (Pattern AddMul)) : Pattern AddMul := Pattern.PatTerm h args

-- Create patterns for add/mul operators and lit
def addP (a b : Pattern AddMul) := pTerm AddMul.add [a, b]
def mulP (a b : Pattern AddMul) := pTerm AddMul.mul [a, b]
def litP (n : Nat)              := pTerm (AddMul.lit n) []
def varP (s : String)           := pTerm (AddMul.var s) []
-- A bit confusing but pVar is like ?x and varP is like x
-- No idea if we need varP but I have a constructor for it
-- so I might as well bring it in for now and think later
-- TODO: think

-- ehm does this work? i guess. is this efficient? probably not.
-- Can make macro for rewrite rules r* ( lhs === rhs )
-- TODO: probably read "metaprogramming in lean 4" and get smth nicer...
macro "r*" lhs:term " === " rhs:term : term =>
  `({ lhs := $lhs, rhs := $rhs })

macro "?" lhs:term : term => `(pVar $lhs)

-- By Macro (find a better one)
def ruleAddComm'' : Rule AddMul :=
  r* (addP (?"a") (?"b")) === (addP (?"b") (?"a"))


/-
  Tests for rewrite rules. Rules can be defined inside and outside tests
  Use:
  def ruleXX : Rule α := {
    lhs := (Pattern α)
    rhs := (Pattern α)
  }
  To define a rule outside of a test (global scope)

  or:
  let ruleXX : Rule α := {
    \*same as above\*
  }
  To define a rule locally (see testAddZero)
-/

-- Example Rules
/-
def ruleAddComm : Rule AddMul := {
  lhs := addP (pVar "a") (pVar "b"), -- (+ ?a ?b)
  rhs := addP (pVar "b") (pVar "a")  -- (+ ?b ?a)
}
-/


/-
  Examples of locally defined rules
-/
def ruleAddComm : Rule AddMul :=
  r* addP (?"a") (?"b") === addP (?"b") (?"a")


def ruleMulZero : Rule AddMul :=
  r* mulP (?"a") (litP 0) === (litP 0)

-- Using such rule
def testAddComm : EGraphIO Unit := do
  IO.println "\nTest: x + y → y + x"

  let x ← runLine <| push { head := .var "x", args := [] }
  let y ← runLine <| push { head := .var "y", args := [] }
  let _ ← runLine <| push { head := .add, args := [x, y] }

  printEGraph

  eqSat (α := AddMul) [ruleAddComm]

  printEGraph

#eval runTest testAddComm "AddComm"

-- Defining rule inside test
def testAddZero : EGraphIO Unit := do
  IO.println "\nTest: x + 0 → x"

  let ruleAddZero : Rule AddMul :=
    r* addP (?"x") (litP 0) === (?"x")


  let x    ← runLine <| push { head := .var "x", args := [] }
  let z ← runLine <| push { head := .lit 0, args := [] }

  let _ ← runLine <| push { head := .add, args := [x, z] }

  printEGraph

  -- TODO: any difference here...?
  -- Guess: not
  eqSat (α := AddMul) [ruleAddZero]
  -- let _ ← runSchedule (α := AddMul) [ruleAddZero]

  printEGraph

#eval runTest testAddZero "Add Zero"

def testDouble : EGraphIO Unit := do
  IO.println "\nTest: x + x → 2 * x"

  let ruleDouble : Rule AddMul := {
    lhs := addP (pVar "x") (pVar "x"),
    rhs := mulP (litP 2) (pVar "x")
  }

  let a ← runLine <| push { head := .var "a", args := [] }
  let two ← runLine <| push { head := .lit 2, args := [] }

  let _expr ← runLine <| push { head := .add, args := [a, a] }
  let _target ← runLine <| push { head := .mul, args := [two, a] }

  printEGraph

  eqSat [ruleDouble]

  printEGraph

#eval runTest testDouble

/-
  Caught a non-canonical insertion bug
  Idea:
    let a, b
    let a ≣ b
    let a + b
    Q: Will it rewrite?
-/

/-
  Caught a non-canonical id insertion in ematch
  Repair was using non-canonical values
-/
def testRewriteCatchEquivalence : EGraphIO Unit := do
  IO.println "\nTest: Rewrite catches Equivalence?"

  let ruleDouble : Rule AddMul :=
    r* addP (?"x") (?"x") === mulP (litP 2) (?"x")

  let a ← runLine <| push { head := .var "a", args := [] }
  let b ← runLine <| push { head := .var "b", args := [] }
  let _ ← runLine <| push { head := .add    , args := [a, b]}
  printEGraph
  let _ ← runLine <| union a b
  printEGraph
  -- let _ ← runLineUnit <| rebuild
  printEGraph

  eqSat [ruleDouble]
  let _ ← runLineUnit <| rebuild
  printEGraph

#eval runTest testRewriteCatchEquivalence

def testRewriteViaEquivalence : EGraphIO Unit := do
  IO.println "\nTest: Rewrite via Equivalence"

  let ruleDouble : Rule AddMul := {
    lhs := addP (pVar "x") (pVar "x"),
    rhs := mulP (litP 2) (pVar "x")
  }
  let a ← runLine <| push { head := .var "a", args := [] }
  let b ← runLine <| push { head := .var "b", args := [] }

  -- a ≡ b
  printEGraph
  let _ ← runLine <| union a b
  -- let _ ← runLineUnit <| rebuild
  printEGraph
  let two ← runLine <| push { head := .lit 2, args := [] }

  let _ ← runLine <| push { head := .add, args := [a, b] }
  let _ ← runLine <| push { head := .mul, args := [two, b] }

  printEGraph
  eqSat [ruleDouble]
  printEGraph

#eval runTest testRewriteViaEquivalence
