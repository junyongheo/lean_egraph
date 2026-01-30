-- https://github.com/egraphs-good/egglog/blob/main/tests/integer_math.egg

import Leanegraph.core
import Leanegraph.framework

variable {α : Type _} [Hashable α]

open EGraph

inductive MathLang where
| diff
| integral
| add
| sub
| mul
| div
| pow
| lshift
| rshift
| mod_
| not_
| const : Int → MathLang
| sym : String → MathLang
deriving Repr, DecidableEq, Hashable

instance : ToString MathLang where
  toString
  | .const n => s!"{n}"
  | .sym s   => s
  | .add     => "+"
  | .sub     => "-"
  | .mul     => "*"
  | .div     => "/"
  | .diff       => "δ" -- i think..?
  | .integral       => "∫"
  | .pow     => "^"
  | .lshift    => "<<"
  | .rshift    => ">>"
  | .mod_    => "%"
  | .not_    => "!"

instance : ParseExpr MathLang where
  parse sx := match sx with
  | .atom s =>
    match s.toInt? with
    | some n => some (.const n, [])
    | none   => some (.sym s, [])
  | .list (head :: args) =>
    match head with
    | .atom "Add"      => some (.add, args)
    | .atom "Sub"      => some (.sub, args)
    | .atom "Mul"      => some (.mul, args)
    | .atom "Div"      => some (.div, args)
    | .atom "Pow"      => some (.pow, args)
    | .atom "RShift"   => some (.rshift, args)
    | .atom "LShift"   => some (.lshift, args)
    | .atom "Mod"      => some (.mod_, args)
    | .atom "Not"      => some (.not_, args)
    | .atom "Diff"     => some (.diff, args)
    | .atom "Integral" => some (.integral, args)
    | _ => none
  | .list [] => none

structure MathLangData where
  data : Option Int
deriving Inhabited, Repr

def myMake (en : ENode MathLang) (children : Array MathLangData) : MathLangData :=
  -- dbg_trace s!"ENode {en.head} Has Children? {!children.isEmpty}"
  let x :=
    (
      if children.isEmpty then
        (λ _ => none)
      else
        (λ i => (children[i]!).data) : (Nat → Option Int)
    )
  match en.head, en.args with
  | .const n, _ => {data := some n}
  | .add, _    => match x 0, x 1 with | some a, some b => {data := some (a + b)} | _, _ => {data := none}
  | .sub, _    => match x 0, x 1 with | some a, some b => {data := some (a - b)} | _, _ => {data := none}
  | .mul, _    => match x 0, x 1 with | some a, some b => {data := some (a * b)} | _, _ => {data := none}
  | .div, _    => match x 0, x 1 with
                  | some a, some b => if b != 0 then {data := some (a / b)} else {data := none}
                  | _, _ => {data := none}
  | .lshift, _ => match x 0, x 1 with | some a, some b => {data := some (a.shiftLeft b.natAbs)} | _, _ => {data := none}
  | .rshift, _ => match x 0, x 1 with | some a, some b => {data := some (a.shiftRight b.natAbs)} | _, _ => {data := none}
  | .not_, _   => match x 0        with | some a         => {data := some (~~~a)} | _ => {data := none}
  | _, _ => {data := none}

def myJoin (d1 : MathLangData) (d2 : MathLangData) : MathLangData :=
  match d1.data, d2.data with
  | some v1, some v2 => if v1 == v2 then d1 else d1
  | some _, _ => d1
  | _, some _ => d2
  | _, _ => {data := none}

instance ConstantFold : EGraph.Analysis MathLang MathLangData where
  make := myMake
  join := myJoin
  modify eg id :=
    -- Inject computed constants into the graph
    let data := (eg.ecmap.get! id).data
    match data.data with
    | none => eg
    | some n =>
        let update : EGraphM MathLang MathLangData Unit := do
           let constId ← push { head := .const n, args := #[] } myMake
           let _ ← union id constId myJoin
           return ()
        let (_, eg') := update.run eg
        eg'

def liftTerm (h : MathLang) (args : List (Pattern MathLang)) : Pattern MathLang := Pattern.PatTerm h (Array.mk args)
def liftVar (s : String) : Pattern MathLang := Pattern.PatVar s

-- prefix:100 "?" => Pattern.PatVar

def pAdd (a b : Pattern MathLang) := liftTerm .add [a, b]
def pSub (a b : Pattern MathLang) := liftTerm .sub [a, b]
def pMul (a b : Pattern MathLang) := liftTerm .mul [a, b]
def pDiv (a b : Pattern MathLang) := liftTerm .div [a, b]
def pPow (a b : Pattern MathLang) := liftTerm .pow [a, b]
def pLSh (a b : Pattern MathLang) := liftTerm .lshift [a, b]
def pRSh (a b : Pattern MathLang) := liftTerm .rshift [a, b]
def pNot (a : Pattern MathLang)   := liftTerm .not_ [a]
def pConst (n : Int)              := liftTerm (.const n) []

def isNotZero (var : String) : Dict MathLang → EGraphM MathLang MathLangData Bool :=
  λ dict => do
    let id := dict.get! var
    let cid ← lookupCanonicalEClassId id
    let eg ← get
    let analysis := (eg.ecmap.get! cid).data
    match analysis.data with
    | some n =>
      -- if n == 0 then return false else return true
      return (n != 0)
    | none   => return true



def isConst (var : String) : Dict MathLang → EGraphM MathLang MathLangData Bool :=
  λ (dict) => (
    do
      let id := dict.get! var
      let cid ← lookupCanonicalEClassId id
      let eg ← get
      let analysis := (eg.ecmap.get! cid).data
      match analysis.data with
      | some _ => return true
      | none   => return false
  )


abbrev MathRule := Rule MathLang MathLangData

def integerMathRules : List MathRule := [

  r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
  r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
  r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c"),
  r* pMul (?"a") (pMul (?"b") (?"c")) === pMul (pMul (?"a") (?"b")) (?"c"),

  r* pSub (?"a") (?"b") === pAdd (?"a") (pMul (pConst (-1)) (?"b")),

  r* pAdd (?"a") (pConst 0) === (?"a"),
  r* pMul (?"a") (pConst 0) === (pConst 0),
  r* pMul (?"a") (pConst 1) === (?"a"),

  r* pSub (?"a") (?"a") === (pConst 0),
  r* pDiv (?"a") (?"a") === (pConst 1) if isNotZero "a",

  r* pMul (?"a") (pAdd (?"b") (?"c")) === pAdd (pMul (?"a") (?"b")) (pMul (?"a") (?"c")),
  r* pAdd (pMul (?"a") (?"b")) (pMul (?"a") (?"c")) === pMul (?"a") (pAdd (?"b") (?"c")),

  r* pMul (pPow (?"a") (?"b")) (pPow (?"a") (?"c")) === pPow (?"a") (pAdd (?"b") (?"c"))
     ifMultiple [(isNotZero "b"), (isNotZero "c")],

  r* pPow (?"x") (pConst 0) === (pConst 1) if isNotZero "x",
  r* pPow (?"x") (pConst 1) === (?"x"),
  r* pPow (?"x") (pConst 2) === pMul (?"x") (?"x"),

  r* pPow (?"x") (pConst (-1)) === pDiv (pConst 1) (?"x") if isNotZero "x",

  r* pDiv (?"a") (?"b") === pMul (?"a") (pPow (?"b") (pConst (-1))) if isNotZero "b",

  r* pMul (?"x") (pPow (?"c") (?"y")) === pLSh (?"x") (?"y") if isConst "c",
  r* pDiv (?"x") (pPow (?"c") (?"y")) === pRSh (?"x") (?"y") if isConst "c",

  r* pNot (pNot (?"x")) === (?"x")
]

-- ==========================================
-- 7. Test Execution
-- ==========================================
def integerMathTest : EGraphGenericIO MathLang MathLangData Unit := do
  IO.println "--- Integer Math Test (Fix Panic) ---"

  -- Start: (a * 2^3) / (c + (b*2 - b*2))
  printEGraph
  let startExpr ← pushTerm "(Div (Mul a (Pow  2 3)) (Add c (Sub (Mul b 2) (Mul b 2))))"
  printEGraph
  -- Equiv: (a << 3) / (c * !!1)
  let equivExpr ← pushTerm "(Div (LShift a 3) (Mul c (Not (Not 1))))"


  eqSat (rules := integerMathRules) (limit := 5)

  let _ ← checkEquivalent startExpr equivExpr
