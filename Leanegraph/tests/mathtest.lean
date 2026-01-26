import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers
import Leanegraph.framework.extraction
import Leanegraph.languages.mathlang
import Leanegraph.framework.macros

open EGraph
open MathLang

def testAnalysisCF : MathLangIO Unit := do
  let c1 ← push (.const 1)
  -- runLine <| pushRun { head := MathLang.const 1, args := [] }
  let c2 ← push (.const 2)
  -- runLine <| pushRun { head := MathLang.const 2, args := [] }
  printEGraph
  let cf ← push .add [c1, c2]
  --runLine <| pushRun { head := MathLang.add, args := [c1, c2] }
  printEGraph
  let _ ← rebuild
  printEGraph


-- #eval runTest testAnalysisCF


def testAssocAdd : MathLangIO Unit := do
  IO.println "\nTest Constant Folding"

  let subsetRules : List MathRule := [
    r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
    r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
    r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c")
    ]

  let sat ← runLine <| pushRun {head := .const 1, args := []}
  let dua ← runLine <| pushRun {head := .const 2, args := []}
  let tig ← runLine <| pushRun {head := .const 3, args := []}
  let mpt ← runLine <| pushRun {head := .const 4, args := []}
  let lim ← push (.const 5)
  let enm ← push (.const 6)

  let lpe ← push .add [lim, enm]
  let mpl ← push .add [mpt, lpe]
  let tpm ← push .add [tig, mpl]
  let tpt ← push .add [dua, tpm]

  -- LHS
  let st ← push .add [sat, tpt]


  printEGraph
  eqSat (α := MathLang) (rules := subsetRules) (limit := 10)
  printEGraph

-- #eval runTest testAssocAdd "ConstFold"

def quickerAssocAdd : MathLangIO Unit := do
  let st ← pushTerm ("(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7)))))))")

  -- printEGraph
  eqSat (limit := 4) [
    r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
    r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
    r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c")
    ]
  printEGraph
  let rhs ← pushTerm ("(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1)))))))")

  let _ ← checkEquivalent st rhs

  IO.println s!"Did we win?"

-- #eval runTest quickerAssocAdd

def halfAutomated : MathLangIO Unit := do
    test_fn
      (lhs :=  ("+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"))
      (rhs := [("+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))")])
      (rules := [
      r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
      r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
      r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c")
      ])

-- #eval runTest halfAutomated

/-

-- Figure out how to pass α and D explicitly...
def automatedAssocAdd : IO Unit := do
  test_fn_self
    (lhs :=  ("+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"))
    (rhs := [("+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))")])
    (rules := [
    r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
    r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
    r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c")
    ])

#eval automatedAssocAdd
-/
def math_simplify_const : MathLangIO Unit := do -- takes 3 iterations, use as benchmark? does take forever
  let gl ← push (.const 1)
  printEGraph
  let st ← pushTerm "(+ 1 (- a (* (- 2 1) a)))"
  printEGraph
  eqSat (rules := [ -- because of egraph explosion it's really unmanageable with the full set thanks egg
    r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
    r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
    r* pAdd (?"a") (pConst 0) === (?"a"),
    r* pAdd (pConst 0) (?"a") === (?"a"),
    r* pMul (?"a") (pConst 1) === (?"a"),
    r* pMul (pConst 1) (?"a") === (?"a"),
    r* pMul (?"a") (pConst 0) === pConst 0,
    r* pMul (pConst 0) (?"a") === pConst 0,
    r* pSub (?"a") (?"a") === pConst 0,
    r* pSub (?"a") (pConst 0) === (?"a")

  ]) (limit := 3)
  printEGraph
  let _ ← checkEquivalent st gl
-- #eval runTest test1

def math_fail : MathLangIO Unit := do
  let lhs ← pushTerm "(+ x y)"
  let rhs ← pushTerm "(/ x y)"

  eqSat (rules := mathRules) (limit := 2)

  let _ ← checkNonEquivalent lhs rhs

def math_simplify_add : MathLangIO Unit := do
  let lhs ← pushTerm "(+ x (+ x (+ x x)))"
  let rhs ← pushTerm "(* 4 x)"
  eqSat (rules := mathRules) (limit := 2)
  let _ ← checkEquivalent lhs rhs

#eval runTest math_simplify_add

def math_powers : MathLangIO Unit := do
  let lhs ← pushTerm "(* (pow 2 x) (pow 2 y))"
  let rhs ← pushTerm "(pow 2 (+ x y))"
  eqSat (rules := mathRules) (limit := 2)
  let _ ← checkEquivalent lhs rhs

def math_simplify_root : MathLangIO Unit := do
  let lhs ← pushTerm "(/ 1
       (- (/ (+ 1 (sqrt five))
             2)
          (/ (- 1 (sqrt five))
             2)))"
  let rhs ← pushTerm "(/ 1 (sqrt five))"
  eqSat (rules := mathRules) (limit := 2) (nodeLimit := 75000)
  let _ ← checkEquivalent lhs rhs

def math_simplify_factor : MathLangIO Unit := do
    let lhs ← pushTerm "(* (+ x 3) (+ x 1))"
    let rhs ← pushTerm "(+ (+ (* x x) (* 4 x)) 3)"
    eqSat (rules := mathRules) (limit := 3)
    let _ ← checkEquivalent lhs rhs

-- #eval runTest math_simplify_factor
