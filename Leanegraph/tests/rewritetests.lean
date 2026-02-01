import Leanegraph.languages.addmul
import Leanegraph.framework
import Leanegraph.core

/-
  WIP
-/

open EGraph

variable {α : Type _} [DecidableEq α] [Hashable α]

/-
  Helpers for the AddMul Language
  TODO: rewrite them to be generic
-/

-- Lift var/term → Pattern
/-
def liftVar (s : String) : Pattern AddMul := Pattern.PatVar s
def liftTerm (h : AddMul) (args : List (Pattern AddMul)) : Pattern AddMul := Pattern.PatTerm h (Array.mk args)
-/


-- Create patterns for add/mul operators and lit
/-
def pAdd (a b : Pattern AddMul) := liftTerm AddMul.add [a, b]
def pMul (a b : Pattern AddMul) := liftTerm AddMul.mul [a, b]
def pLit (n : Nat)              := liftTerm (AddMul.lit n) []
def pVar (s : String)           := liftTerm (AddMul.var s) []
-/
-- A bit confusing but pVar is like ?x and pVar is like x
-- No idea if we need pVar but I have a constructor for it
-- so I might as well bring it in for now and think later
-- TODO: think

-- ehm does this work? i guess. is this efficient? probably not.
-- Can make macro for rewrite rules r* ( lhs === rhs )
-- TODO: probably read "metaprogramming in lean 4" and get smth nicer...


abbrev AddMulRule := Rule AddMul Unit
-- By Macro (find a better one)
def ruleAddComm'' : AddMulRule :=
  r* (pAdd (?"a") (?"b")) === (pAdd (?"b") (?"a"))

instance : Inhabited (Pattern AddMul) where
  default := Pattern.PatVar "_"

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
def ruleAddComm : AddMulRule := {
  lhs := pAdd (pVar "a") (pVar "b"), -- (+ ?a ?b)
  rhs := pAdd (pVar "b") (pVar "a")  -- (+ ?b ?a)
}
-/


/-
  Examples of locally defined rules
-/
def ruleAddComm : AddMulRule :=
  r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a")


def ruleMulZero : AddMulRule :=
  r* pMul (?"a") (pLit 0) === (pLit 0)

-- Using such rule
def testAddComm : EGraphIO Unit := do
  IO.println "\nTest: x + y → y + x"

  let x ← push (.var "x")
  let y ← push (.var "y")
  let _ ← push .add [x,y]

  printEGraph

  eqSat (α := AddMul) [ruleAddComm]

  printEGraph

-- #eval runTest testAddComm "AddComm"

-- Defining rule inside test
def testAddZero : EGraphIO Unit := do
  IO.println "\nTest: x + 0 → x"

  let ruleAddZero : AddMulRule :=
    r* pAdd (?"x") (pLit 0) === (?"x")


  let x ← push (.var "x")
  let z ← push (.lit 0)

  let _ ← push .add [x,z]

  printEGraph

  -- TODO: any difference here...?
  -- Guess: not
  eqSat (α := AddMul) [ruleAddZero]
  -- let _ ← runSchedule (α := AddMul) [ruleAddZero]

  printEGraph

-- #eval runTest testAddZero "Add Zero"

def testDouble : EGraphIO Unit := do
  IO.println "\nTest: x + x → 2 * x"

  let ruleDouble : AddMulRule := {
    lhs := pAdd (?"x") (?"x"),
    rhs := pMul (pLit 2) (?"x")
  }

  let a ← push (.var "a")
  let two ← push (.lit 2)

  let expr ← push .add [a, a]
  let target ← push .mul [two, a]

  eqSat [ruleDouble]


  let _ ← checkEquivalent expr target

-- #eval runTest testDouble

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

  let ruleDouble : AddMulRule :=
    r* pAdd (?"x") (?"x") === pMul (pLit 2) (?"x")

  let a ← push (.var "a")
  let b ← push (.var "b")
  let _ ← push .add [a,b]
  -- printEGraph
  let _ ← runLine <| unionRun a b
  -- printEGraph
  let _ ← runLineUnit <| rebuildRun
  -- printEGraph

  eqSat [ruleDouble]
  let _ ← rebuild
  printEGraph


#eval runTest testRewriteCatchEquivalence

/-

-/
def testRewriteViaEquivalence : EGraphIO Unit := do
  IO.println "\nTest: Rewrite via Equivalence"

  let ruleDouble : AddMulRule := {
    lhs := pAdd (?"x") (?"x"),
    rhs := pMul (pLit 2) (?"x")
  }
  let a ← runLine <| pushRun { head := .var "a", args := #[] }
  let b ← runLine <| pushRun { head := .var "b", args := #[] }
  -- a ≡ b
  printEGraph
  let _ ← runLine <| unionRun a b
  let _ ← rebuild
  printEGraph
  let _ ← runLine <| pushRun { head := .add, args := #[a, b] }


  printEGraph
  eqSat [ruleDouble]
  printEGraph

#eval runTest testRewriteViaEquivalence

def RewritingTests := [
  testAddComm,
  testAddZero,
  testDouble,
  testRewriteCatchEquivalence,
  testRewriteViaEquivalence,
]

-- Hmm I'm not sure how the egraph is supposed to show the infinite cycle
def cycleTest : EGraphIO Unit := do
  let mulZero : AddMulRule := r* (?"x") === pMul (?"x") (pLit 0)

  let a ← runLine <| pushRun { head := .var "a", args := #[] }

  printEGraph

  eqSat [mulZero]

  printEGraph

#eval runTest cycleTest
