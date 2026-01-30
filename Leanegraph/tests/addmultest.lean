import Leanegraph.core
import Leanegraph.framework
import Leanegraph.languages.addmul


open EGraph

def simpleRules : List (Rule AddMul AddMulData) := [
    r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
    r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
    r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c")
]

def quickerAssocAdd : AddMulIO Unit := do
  let st ← parseTerm ("(+ 1 (+ 2 3))")

  printEGraph
  eqSat (limit := 3) (rules := simpleRules)
  printEGraph
  let rhs ← parseTerm ("(+ 3 (+ 2 1))")

  let _ ← checkEquivalent st rhs

#eval runTest quickerAssocAdd
