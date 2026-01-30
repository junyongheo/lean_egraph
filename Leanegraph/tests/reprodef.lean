import Leanegraph.core
import Leanegraph.framework

open EGraph

-- 1. Language Definition
inductive Group where
| i | A | B | a | b     -- Constants: I, A, B, a, b
| mul | inv             -- Operators: *, inv
deriving DecidableEq, Hashable, Repr

instance : ToString Group where
  toString
  | .i => "I"
  | .A => "A" | .B => "B"
  | .a => "a" | .b => "b"
  | .mul => "*" | .inv => "inv"

instance : Analysis Group Unit where
  make _ _ := ()
  join _ _ := ()
  modify eg _ := eg

-- 2. Parsers & Patterns
instance : ParseExpr Group where
  parse sx := match sx with
  | .atom "I" => some (.i, [])
  | .atom "A" => some (.A, [])
  | .atom "B" => some (.B, [])
  | .atom "a" => some (.a, [])
  | .atom "b" => some (.b, [])
  | .list (.atom "*" :: args)   => some (.mul, args)
  | .list (.atom "inv" :: args) => some (.inv, args)
  | _ => none

-- Helper macros for patterns
def pMul (x y : Pattern Group) := Pattern.PatTerm .mul #[x, y]
def pInv (x : Pattern Group)   := Pattern.PatTerm .inv #[x]
def pA := Pattern.PatTerm Group.A #[]
def pI := Pattern.PatTerm Group.i #[]

macro "?" lhs:term : term => `(Pattern.PatVar $lhs)

-- 3. Rules
def groupRules : List (Rule Group Unit) := [
  -- Associativity (birewrite = two rules)
  -- (* (* a b) c) <-> (* a (* b c))
  r* (pMul (pMul (?"a") (?"b")) (?"c")) === (pMul (?"a") (pMul (?"b") (?"c"))),
  r* (pMul (?"a") (pMul (?"b") (?"c"))) === (pMul (pMul (?"a") (?"b")) (?"c")),

  -- Identity
  r* (pMul pI (?"a")) === (?"a"),
  r* (pMul (?"a") pI) === (?"a"),

  -- Inverse
  r* (pMul (pInv (?"a")) (?"a")) === pI,
  r* (pMul (?"a") (pInv (?"a"))) === pI,

  -- Cyclic constraint: A^4 = I
  -- Matches specifically: A * (A * (A * A))
  r* (pMul pA (pMul pA (pMul pA pA))) === pI
]

-- 4. Test Suite
def groupTest : EGraphGenericIO Group Unit Unit := do
  IO.println "--- Group Theory Test ---"

  -- Setup Constants and initial definitions
  let A2 ← pushTerm "(* A A)"

  -- (let A4 (g* A2 A2))
  let A4 ← push .mul [A2, A2] -- using IDs directly for clarity

  -- (let A8 (g* A4 A4))
  let A8 ← push .mul [A4, A4]



  -- ==========================================
  -- Test 1: Associativity Expansion
  -- Check: A^8 == (A^2 * A^2) * (A^2 * A^2)
  -- ==========================================
  IO.println "[Test 1] Checking A^8 structure..."

  -- The target term: (* (* A2 A2) (* A2 A2))
  let target1 ← pushTerm s!"(* (* (* A A) (* A A)) (* (* A A) (* A A)))"

  -- Run saturation
  printEGraph
  eqSat (rules := groupRules)
  printEGraph

  let _ ← checkEquivalent A8 target1

  -- ==========================================
  -- Test 2: Deep Associativity
  -- Check: A^8 == A^2 * (A^2 * (A^2 * A^2))
  -- ==========================================
  IO.println "[Test 2] Checking Deep Associativity..."

  let target2 ← pushTerm s!"(* (* A A) (* (* A A) (* (* A A) (* A A))))"

  -- Since we are in the same graph, we continue saturation if needed
  -- (Though A8 was already saturated above)
  eqSat (rules := groupRules)

  IO.println "YEAHHH"

  let _ ← checkEquivalent target1 target2

  -- ==========================================
  -- Test 3: Cancellation (Push/Pop simulated)
  -- Expr: b * (inv a * a) * inv b
  -- Expected: I (Identity)
  -- ==========================================
  IO.println "[Test 3] Cancellation: b * (a^-1 * a) * b^-1"

  let t3 ← pushTerm "(* (* b (* (inv a) a)) (inv b))"
  let i  ← pushTerm "I"

  -- Logic:
  -- 1. (* (inv a) a) -> I
  -- 2. (* b I) -> b
  -- 3. (* b (inv b)) -> I

  eqSat (rules := groupRules)

  let _ ← checkEquivalent t3 i

  IO.println "--- Test Complete ---"

-- #eval runTest groupTest
