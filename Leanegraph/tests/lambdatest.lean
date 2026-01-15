import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers
import Leanegraph.languages.lambda

/-
  This one is incomplete, due to
  - Definitive Issues
    - Lack of analysis, non-capture functionalities means I can't port the tests yet
  - Possible Issues
    - Idk I think the language isn't defined properly
-/

open EGraph

-- Lift var/term → Pattern
def liftTerm (h : Lambda) (args : List (Pattern Lambda)) : Pattern Lambda := Pattern.PatTerm h args
def liftVar (s : String) : Pattern Lambda := Pattern.PatVar s

-- Constructors for data(?) types
def pNum (n : Int)    := liftTerm (.num n) []
def pBool (b : Bool)  := liftTerm (.bool b) []
def pVar (s : String) := liftTerm (.var s) []

-- Constructors for operators
-- TODO: maybe it's important to enforce number of arguments at the language definition level?
def pAdd (a b : Pattern Lambda)   := liftTerm .add [a, b]
def pEq (a b : Pattern Lambda)    := liftTerm .eq [a, b]
def pApp (f x : Pattern Lambda)   := liftTerm .app [f, x]
def pLam (v b : Pattern Lambda)   := liftTerm .lam [v, b]
def pLet (v e b : Pattern Lambda) := liftTerm .let_ [v, e, b]
def pFix (v e : Pattern Lambda)   := liftTerm .fix [v, e]
def pIf (c t e : Pattern Lambda)  := liftTerm .if_ [c, t, e]

-- Macros for syntax
macro "?" lhs:term : term => `(liftVar $lhs)

macro "r*" lhs:term " === " rhs:term : term =>
  `({ lhs := $lhs, rhs := $rhs })


def lambdaRules : List (Rule Lambda) := [
  -- Open term rules
  r* pIf (pBool true) (?"then") (?"else")  === (?"then"),
  r* pIf (pBool false) (?"then") (?"else") === (?"else"),

  -- if-elim: (if (= (var ?x) ?e) ?then ?else) -> ?else
  {(r* pIf (pEq (?"x") (?"e")) (?"then") (?"else") === (?"else") : Rule Lambda) with
    cnd := [
      Condition.Equal (pLet (?"x") (?"e") (?"then")) (pLet (?"x") (?"e") (?"else"))
    ]
  },

  -- Add-Comm
  r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
  -- Add-Assoc
  r* pAdd (pAdd (?"a") (?"b")) (?"c") === pAdd (?"a") (pAdd (?"b") (?"c")),
  -- Eq-Comm
  r* pEq (?"a") (?"b") === pEq (?"b") (?"a"),

  -- Substitution rules
  r* pFix (?"v") (?"e") === pLet (?"v") (pFix (?"v") (?"e")) (?"e"),
  -- β-Reduction:
  r* pApp (pLam (?"v") (?"body")) (?"e") === pLet (?"v") (?"e") (?"body"),
  -- Let App/Add/Eq
  r* pLet (?"v") (?"e") (pApp (?"a") (?"b")) === pApp (pLet (?"v") (?"e") (?"a")) (pLet (?"v") (?"e") (?"b")),
  r* pLet (?"v") (?"e") (pAdd (?"a") (?"b")) === pAdd (pLet (?"v") (?"e") (?"a")) (pLet (?"v") (?"e") (?"b")),
  r* pLet (?"v") (?"e") (pEq (?"a") (?"b"))  === pEq (pLet (?"v") (?"e") (?"a")) (pLet (?"v") (?"e") (?"b")),

  -- Let Const not possible yet...?

  -- let if
  r* pLet (?"v") (?"e") (pIf (?"cond") (?"then") (?"else")) ===
     pIf (pLet (?"v") (?"e") (?"cond")) (pLet (?"v") (?"e") (?"then")) (pLet (?"v") (?"e") (?"else")),

  -- let var same diff
  r* pLet (?"v1") (?"e") (?"v1") === (?"e"),
  {((r* pLet (?"v1") (?"e") (?"v2") === (?"v2")) : Rule Lambda) with
    cnd := [
      Condition.NotEqual (?"v1") (?"v2")
    ]
  },

  r* pLet (?"v1") (?"e") (pLam (?"v1") (?"body")) === pLam (?"v1") (?"body"),

  -- ok I cannot let lam diff


]

-- For no analysis purposes
def arithmeticRules : List (Rule Lambda) := [
  r* pAdd (pNum 0) (pNum 1) === pNum 1,
  r* pAdd (pNum 1) (pNum 0) === pNum 1,
  r* pEq (pNum 1) (pNum 1)  === pBool true,
  r* pEq (pNum 0) (pNum 0)  === pBool true
]

def allRules := lambdaRules ++ arithmeticRules


def testLambdaUnder : LambdaIO Unit := do
  IO.println "\nTest: Lambda Under"

  let x ← runLine <| push { head := .var "x", args := []}
  let y ← runLine <| push { head := .var "y", args := []}
  let t ← runLine <| push { head := .num 3, args := []}

  let l ← runLine <| push { head := .lam, args := [y, y]}

  let a ← runLine <| push { head := .app, args := [l, t]}

  let inner ← runLine <| push {head := .add, args := [t, a]}

  let _st ← runLine <| push { head := .lam, args := [x, inner]}

  let s ← runLine <| push { head := .num 6, args := [] }
  let _fn ← runLine <| push { head := .lam, args := [x, s]}

  printEGraph
  eqSat (allRules)
  printEGraph

#eval runTest testLambdaUnder

def testLambdaIfElim : LambdaIO Unit := do
  IO.println "\nTest: Lambda If Elim"


  let a ← runLine <| push { head := .var "a", args := [] }
  let b ← runLine <| push { head := .var "b", args := [] }

  let eqAA  ← runLine <| push { head := .eq, args := [a, b] }
  let _true ← runLine <| push { head := .bool true, args := [] }

  let ruleRefl : Rule Lambda := r* pEq (?"x") (?"x") === pBool true

  let plusAA ← runLine <| push { head := .add, args := [a, a] }
  let plusAB ← runLine <| push { head := .add, args := [a, b] }

  let expr ← runLine <| push { head := .if_, args := [eqAA, plusAA, plusAB] }

  printEGraph
  eqSat (allRules ++ [ruleRefl])
  -- printEGraph

  let _ ← runLine <| checkSameClass expr plusAB "If-True-Elimination"
  printEGraph

#eval runTest testLambdaIfElim "Lambda If Elim"
