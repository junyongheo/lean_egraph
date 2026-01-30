import Leanegraph.core
import Leanegraph.framework
import Leanegraph.languages.prop

open EGraph

def testContrapositive : PropIO Unit := do
  IO.println "\nTest Contrapositive"

  -- These could also be macros...
  -- Left Hand Side
  let x ← runLine <| pushRun {head := .sym "x", args := #[]}
  let y ← runLine <| pushRun {head := .sym "y", args := #[]}
  let st← runLine <| pushRun {head := .impl, args := #[x, y]}
  printEGraph
  eqSat (α := PropLang) (propRules)
  printEGraph

  -- Check if all RHS are found
  let nx ← runLine <| pushRun {head := .not, args := #[x]}
  let ny ← runLine <| pushRun {head := .not, args := #[y]}
  let nny← runLine <| pushRun {head := .not, args := #[ny]}
  let t1 ← runLine <| pushRun {head := .or, args := #[nx, y]}
  let t2 ← runLine <| pushRun {head := .or, args := #[nx, nny]}
  let t3 ← runLine <| pushRun {head := .or, args := #[nny, nx]}
  let t4 ← runLine <| pushRun {head := .impl, args := #[ny, nx]}

  checkSameClassTests st t1
  checkSameClassTests st t2
  checkSameClassTests st t3
  checkSameClassTests st t4

  -- let _ ← runLine <| checkSameClass st t1 "Test 1"
  -- let _ ← runLine <| checkSameClass st t2
  -- let _ ← runLine <| checkSameClass st t3
  -- let _ ← runLine <| checkSameClass st t4

-- #eval runTest testContrapositive

def testProveChain : PropIO Unit := do
  IO.println "\nTest Chain (Transitivity)"

  let x  ← runLine <| pushRun {head := .sym "x", args := #[]}
  let y  ← runLine <| pushRun {head := .sym "y", args := #[]}
  let z  ← runLine <| pushRun {head := .sym "z", args := #[]}
  let xy ← runLine <| pushRun {head := .impl, args := #[x, y]}
  let yz ← runLine <| pushRun {head := .impl, args := #[y, z]}
  -- LHS
  let st ← runLine <| pushRun {head := .and,  args := #[xy, yz]}

  printEGraph
  eqSat (α := PropLang) smallerSet (limit := 5)
  printEGraph

  -- Build RHS
  let nx   ← runLine <| pushRun {head := .not, args := #[x]}
  let ny   ← runLine <| pushRun {head := .not, args := #[y]}

  -- 1. (& (-> (~ y) (~ x)) (-> y z))
  let ny_nx ← runLine <| pushRun {head := .impl, args := #[ny, nx]}
  let t1    ← runLine <| pushRun {head := .and,  args := #[ny_nx, yz]}

  -- 2. (& (-> y z) (-> (~ y) (~ x)))
  let t2    ← runLine <| pushRun {head := .and,  args := #[yz, ny_nx]}

  -- 3. (| z (~ x))
  let t3    ← runLine <| pushRun {head := .or,   args := #[z, nx]}

  -- 4. (| (~ x) z)
  let t4    ← runLine <| pushRun {head := .or,   args := #[nx, z]}

  -- 5. (-> x z)
  let t5    ← runLine <| pushRun {head := .impl, args := #[x, z]}

  let _ ← runLine <| checkSameClass st t1
  let _ ← runLine <| checkSameClass st t2
  let _ ← runLine <| checkSameClass st t3
  let _ ← runLine <| checkSameClass st t4
  let _ ← runLine <| checkSameClass st t5

-- #eval runTest testProveChain "ProveChain"


def testConstFold : PropIO Unit := do
  IO.println "\nTest Constant Folding"

  let t ← runLine <| pushRun {head := .bool true,  args := #[]}
  let f ← runLine <| pushRun {head := .bool false, args := #[]}
  let ft ← runLine <| pushRun {head := .and, args := #[f, t]}
  let tf ← runLine <| pushRun {head := .and, args := #[t, f]}

  -- LHS
  let st ← runLine <| pushRun {head := .or,  args := #[ft, tf]}

  printEGraph
  eqSat (α := PropLang) (propRules)
  printEGraph

  let _ ← runLine <| checkSameClass st f "Folded to False"

-- #eval runTest testConstFold "ConstFold"

def propTests : List (PropIO Unit) := [
  testContrapositive, testProveChain, testConstFold
]

def testAutomated : PropIO Unit := do
  IO.println "\n Test String to EG"

  let implxy := "(→ (¬ x y) z)"

  match ExprParser.SExprParser.run implxy with
  | .ok theStr => runLine <| buildEGFromSExprGeneric theStr
  | .error e  => panic! s!"This did not work with error {e}"

  printEGraph

-- #eval runTest testAutomated

def testAutomatedChain : PropIO Unit := do
  IO.println "\nTest Chain (Transitivity)"

  let st ← parseTerm "(& (→ x y) (→ y z))"

  printEGraph
  eqSat (α := PropLang) smallerSet (limit := 5)
  printEGraph


  -- 1. (& (-> (~ y) (~ x)) (-> y z))
  let r1 ← parseTerm "(& (→ (¬ y) (¬ x)) (→ y z))"
  -- 2. (& (-> y z) (-> (~ y) (~ x)))
  let r2 ← parseTerm "(& (→ y z) (→ (¬ y) (¬ x)))"

  -- 3. (| z (~ x))
  let r3 ← parseTerm "(| z (¬ x))"

  -- 4. (| (~ x) z)
  let r4 ← parseTerm "(| (¬ x) z)"

  -- 5. (-> x z)
  let t5 ← parseTerm "(→ x z)"

  let _ ← runLine <| checkSameClass st r1
  let _ ← runLine <| checkSameClass st r2
  let _ ← runLine <| checkSameClass st r3
  let _ ← runLine <| checkSameClass st r4
  let _ ← runLine <| checkSameClass st t5

-- #eval runTest testProveChain "ProveChain"
/-
def fullyAutomated : IO Unit := do
  test_fn_self
    (lhs := "(& (→ x y) (→ y z))")
    (rhs := [
      "(& (→ (¬ y) (¬ x)) (→ y z))",
      "(& (→ y z) (→ (¬ y) (¬ x)))",
      "(| z (¬ x))",
      "(| (¬ x) z)",
      "(→ x z)"
    ])
    (rules := smallerSet)
    (iterLimit := 5)
    (printLeft := true)
    (printRight := false)
-/
 -- #eval fullyAutomated
