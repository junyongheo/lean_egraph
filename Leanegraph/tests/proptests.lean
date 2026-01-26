import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers
import Leanegraph.languages.prop

open EGraph

def checkSameClassTests (id1 id2 : EClassId) (test : String := "") : PropIO Unit := do
  let st ← get
  let (_,c1) := st.uf.find! id1
  let (_,c2) := st.uf.find! id2

  if c1 != c2 then
    IO.println s!" FAIL: {test}"
    IO.println s!" ID {id1} -> Class {c1}"
    IO.println s!" ID {id2} -> Class {c2}"

def liftVar (s : String) : Pattern PropLang := Pattern.PatVar s
def liftTerm (h : PropLang) (args : List (Pattern PropLang)) : Pattern PropLang := Pattern.PatTerm h args

-- maybe I went a little overboard with matching spacing
def pBool(b   : Bool               ) := liftTerm (.bool b) []
def pAnd (a b : Pattern <| PropLang) := liftTerm (.and   ) [a, b]
def pOr  (a b : Pattern <| PropLang) := liftTerm (.or    ) [a, b]
def pNot (a   : Pattern <| PropLang) := liftTerm (.not   ) [a]
def pImpl(a b : Pattern <| PropLang) := liftTerm (.impl  ) [a, b]
def pSym (s   : String             ) := liftTerm (.sym s ) []

macro "?" lhs:term : term => `(liftVar $lhs)

macro "r*" lhs:term " === " rhs:term : term =>
  `({ lhs := $lhs, rhs := $rhs})

-- Make it cleaner by restructuring this as smallerSet ++ (distributive rules)
def propRules : List (Rule PropLang Unit) := [
  -- Def Imply
  r* pImpl (?"a") (?"b") === pOr (pNot (?"a")) (?"b"),
  -- Imply Flip
  r* pOr (pNot (?"a")) (?"b") === pImpl (?"a") (?"b"),
  -- Double Neg
  r* pNot (pNot (?"a")) === (?"a"),
  -- Double Neg Flip
  r* ?"a" === pNot (pNot (?"a")), -- is the parenthesis necessary
  -- Assoc Or
  r* pOr (pOr (?"a") (?"b")) (?"c") === pOr (?"a") (pOr (?"b") (?"c")),
  -- Dist and Or
  r* pAnd (?"a") (pOr (?"b") (?"c")) === pOr (pAnd (?"a") (?"b")) (pAnd (?"a") (?"c")),
  -- Dist Or And
  r* pOr (?"a") (pAnd (?"b") (?"c")) === pAnd (pOr (?"a") (?"b")) (pOr (?"a") (?"c")),
  -- Commutativity
  r* pOr (?"a") (?"b")  === pOr (?"b") (?"a"),
  r* pAnd (?"a") (?"b") === pAnd (?"b") (?"a"),
  -- Lem
  r* pOr (?"a") (pNot (?"a")) === pBool true,
  -- Or True
  r* pOr (?"a") (pBool true) === pBool true,
  -- Or False
  r* pOr (?"a") (pBool false) === (?"a"),
  -- And true
  r* pAnd (?"a") (pBool true) === (?"a"),
  -- And false
  r* pAnd (?"a") (pBool false) === (pBool false),
  -- Contrapositive
  r* pImpl (?"a") (?"b") === pImpl (pNot (?"b")) (pNot (?"a")),
  -- Not True/False
  r* pNot (pBool true) === pBool false,
  r* pNot (pBool false) === pBool true,
]

-- No distributive rules because that absolutely murders my laptop
def smallerSet : List (Rule PropLang Unit) := [
    -- Def Imply
  r* pImpl (?"a") (?"b") === pOr (pNot (?"a")) (?"b"),
  -- Imply Flip
  r* pOr (pNot (?"a")) (?"b") === pImpl (?"a") (?"b"),
  -- Double Neg Flip
  r* ?"a" === pNot (pNot (?"a")), -- is the parenthesis necessary
  -- Lem
  r* pOr (?"a") (pNot (?"a")) === pBool true,
  -- Commutativity
  r* pOr (?"a") (?"b")  === pOr (?"b") (?"a"),
  r* pAnd (?"a") (?"b") === pAnd (?"b") (?"a"),
    -- Or True
  r* pOr (?"a") (pBool true) === pBool true,
  -- Or False
  r* pOr (?"a") (pBool false) === (?"a"),
  -- And true
  r* pAnd (?"a") (pBool true) === (?"a"),
  -- And false
  r* pAnd (?"a") (pBool false) === (pBool false),
  -- Contrapositive
  r* pImpl (?"a") (?"b") === pImpl (pNot (?"b")) (pNot (?"a")),
  -- Not True/False
  r* pNot (pBool true) === pBool false,
  r* pNot (pBool false) === pBool true,
  -- lem_imply (see rust code)
  r* pAnd (pImpl (?"a") (?"b")) (pImpl (pNot (?"a")) (?"c")) === pOr (?"b") (?"c")

]

/-
  Start Tests
-/

/-
  Based on EGG Test
    prove_something(
        "contrapositive",

        "(-> x y)",

        -- equivalent to --

        "(-> x y)",
        "(| (~ x) y)",
        "(| (~ x) (~ (~ y)))",
        "(| (~ (~ y)) (~ x))",
        "(-> (~ y) (~ x))",

}

-/
def testContrapositive : PropIO Unit := do
  IO.println "\nTest Contrapositive"

  -- These could also be macros...
  -- Left Hand Side
  let x ← runLine <| pushRun {head := .sym "x", args := []}
  let y ← runLine <| pushRun {head := .sym "y", args := []}
  let st← runLine <| pushRun {head := .impl, args :=[x, y]}
  printEGraph
  eqSat (α := PropLang) (propRules)
  printEGraph

  -- Check if all RHS are found
  let nx ← runLine <| pushRun {head := .not, args := [x]}
  let ny ← runLine <| pushRun {head := .not, args := [y]}
  let nny← runLine <| pushRun {head := .not, args :=[ny]}
  let t1 ← runLine <| pushRun {head := .or, args := [nx, y]}
  let t2 ← runLine <| pushRun {head := .or, args := [nx, nny]}
  let t3 ← runLine <| pushRun {head := .or, args := [nny, nx]}
  let t4 ← runLine <| pushRun {head := .impl, args := [ny, nx]}

  checkSameClassTests st t1
  checkSameClassTests st t2
  checkSameClassTests st t3
  checkSameClassTests st t4

  -- let _ ← runLine <| checkSameClass st t1 "Test 1"
  -- let _ ← runLine <| checkSameClass st t2
  -- let _ ← runLine <| checkSameClass st t3
  -- let _ ← runLine <| checkSameClass st t4

#eval runTest testContrapositive

def testProveChain : PropIO Unit := do
  IO.println "\nTest Chain (Transitivity)"

  let x  ← runLine <| pushRun {head := .sym "x", args := []}
  let y  ← runLine <| pushRun {head := .sym "y", args := []}
  let z  ← runLine <| pushRun {head := .sym "z", args := []}
  let xy ← runLine <| pushRun {head := .impl, args := [x, y]}
  let yz ← runLine <| pushRun {head := .impl, args := [y, z]}
  -- LHS
  let st ← runLine <| pushRun {head := .and,  args := [xy, yz]}

  printEGraph
  eqSat (α := PropLang) smallerSet (limit := 5)
  printEGraph

  -- Build RHS
  let nx   ← runLine <| pushRun {head := .not, args := [x]}
  let ny   ← runLine <| pushRun {head := .not, args := [y]}

  -- 1. (& (-> (~ y) (~ x)) (-> y z))
  let ny_nx ← runLine <| pushRun {head := .impl, args := [ny, nx]}
  let t1    ← runLine <| pushRun {head := .and,  args := [ny_nx, yz]}

  -- 2. (& (-> y z) (-> (~ y) (~ x)))
  let t2    ← runLine <| pushRun {head := .and,  args := [yz, ny_nx]}

  -- 3. (| z (~ x))
  let t3    ← runLine <| pushRun {head := .or,   args := [z, nx]}

  -- 4. (| (~ x) z)
  let t4    ← runLine <| pushRun {head := .or,   args := [nx, z]}

  -- 5. (-> x z)
  let t5    ← runLine <| pushRun {head := .impl, args := [x, z]}

  let _ ← runLine <| checkSameClass st t1
  let _ ← runLine <| checkSameClass st t2
  let _ ← runLine <| checkSameClass st t3
  let _ ← runLine <| checkSameClass st t4
  let _ ← runLine <| checkSameClass st t5

#eval runTest testProveChain "ProveChain"


def testConstFold : PropIO Unit := do
  IO.println "\nTest Constant Folding"

  let t ← runLine <| pushRun {head := .bool true,  args := []}
  let f ← runLine <| pushRun {head := .bool false, args := []}
  let ft ← runLine <| pushRun {head := .and, args := [f, t]}
  let tf ← runLine <| pushRun {head := .and, args := [t, f]}

  -- LHS
  let st ← runLine <| pushRun {head := .or,  args := [ft, tf]}

  printEGraph
  eqSat (α := PropLang) (propRules)
  printEGraph

  let _ ← runLine <| checkSameClass st f "Folded to False"

#eval runTest testConstFold "ConstFold"

def propTests : List (PropIO Unit) := [
  testContrapositive, testProveChain, testConstFold
]
