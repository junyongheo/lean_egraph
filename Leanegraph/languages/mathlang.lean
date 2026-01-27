import Leanegraph.core
import Leanegraph.framework


variable {α : Type _} [Hashable α]

open EGraph

inductive MathLang where
| d   : MathLang
| i   : MathLang
| add : MathLang
| sub : MathLang
| mul : MathLang
| div : MathLang
| pow : MathLang
| ln  : MathLang
| sqrt: MathLang
| sin : MathLang
| cos : MathLang
| const : Int → MathLang -- Int instead of float because.. well... yeah...
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
  | .d       => "δ" -- i think..?
  | .i       => "∫"
  | .pow     => "^"
  | .ln      => "ln" -- If we know the arguments it would be nicer..? oh but the lang def...
  | .sqrt    => "sqrt"
  | .sin     => "sin"
  | .cos     => "cos"

instance : ParseExpr MathLang where
  parse sx :=
  match sx with
  | .atom s =>
    match s.toNat? with
    | some n => some (.const n, [])
    | none   => some (.sym   s, [])
  | .list (head :: args) =>
    match head with
    | .atom "+"    => some (.add,  args)
    | .atom "-"    => some (.sub,  args)
    | .atom "*"    => some (.mul,  args)
    | .atom "/"    => some (.div,  args)
    | .atom "d"    => some (.d,    args)
    | .atom "i"    => some (.i,    args)
    | .atom "pow"    => some (.pow,  args)
    | .atom "ln"   => some (.ln,   args)
    | .atom "sqrt" => some (.sqrt, args)
    | .atom "sin"  => some (.sin,  args)
    | .atom "cos"  => some (.cos,  args)
    | _ => none
  | .list [] => none



def liftVar (s : String) : Pattern MathLang := Pattern.PatVar s
def liftTerm (h : MathLang) (args : List (Pattern MathLang)) : Pattern MathLang := Pattern.PatTerm h args


def pDiff (x y : Pattern MathLang ) := liftTerm (.d      ) [x, y]
def pIntg (x y : Pattern MathLang ) := liftTerm (.i      ) [x, y]
def pAdd  (x y : Pattern MathLang ) := liftTerm (.add    ) [x, y]
def pSub  (x y : Pattern MathLang ) := liftTerm (.sub    ) [x, y]
def pMul  (x y : Pattern MathLang ) := liftTerm (.mul    ) [x, y]
def pDiv  (x y : Pattern MathLang ) := liftTerm (.div    ) [x, y]
def pPow  (x y : Pattern MathLang ) := liftTerm (.pow    ) [x, y]
def pLn   (x : Pattern MathLang   ) := liftTerm (.ln     ) [x]
def pSqrt (x : Pattern MathLang   ) := liftTerm (.sqrt   ) [x]
def pSin  (x : Pattern MathLang   ) := liftTerm (.sin    ) [x]
def pCos  (x : Pattern MathLang   ) := liftTerm (.cos    ) [x]
def pConst(n : Int                ) := liftTerm (.const n) []
def pSym  (s : String             ) := liftTerm (.sym s  ) []


def MathLangCostFn : costFn MathLang
  | .d => 100
  | .i => 100
  | _  => 1

structure MathLangData where
  data : Option Int

instance : Inhabited (MathLangData) where
  default := {
    data := none
  }

instance : Inhabited (EClass MathLang MathLangData) where
  default := {
    nodes := [],
    parents := [],
    data := default
  }

def myMake (en : ENode MathLang) (children : List MathLangData) : MathLangData :=
  -- dbg_trace s!"ENode {en.head} Has Children? {!children.isEmpty}"
  let x :=
    (
      if children.isEmpty then
        (λ _ => none)
      else
        (λ i => (children[i]!).data) : (Nat → Option Int)
    )
    match en.head, en.args with
    | MathLang.const n, _ =>
      -- dbg_trace s!"WE ARE HERE!!"
      -- dbg_trace s!"Returning some {n}"
      {data := some n}
    | .add, _     =>
      -- Turns out lean is 0 indexed, who knew........
      -- dbg_trace s!"Child data is {x 0} and {x 1}"
      match x 0, x 1 with
      | some a, some b =>
        -- dbg_trace s!"Matched Correctly to some {a + b}"
        {data := some (a + b)}
      | _     , _      => {data := none}
    | .sub, _     =>
      match x 0, x 1 with
      | some a, some b => {data := some (a - b)}
      | _     , _      => {data := none}
    | .mul, _     =>
      match x 0, x 1 with
      | some a, some b => {data := some (a * b)}
      | _     , _      => {data := none}
    | .div, _     =>
      match x 0, x 1 with
      | some a, some b => {data := some (a / b)}
      | _     , _      => {data := none}
    | _, _        => {data := none}


  def myJoin (d1 : MathLangData) (d2 : MathLangData) : MathLangData :=
    match d1.data, d2.data with
    | some v1 , some v2 => if (v1 = v2) then d1 else (panic! s!"Oh nooooo {v1} and {v2}")
    | some _v1, _       => d1
    | _,       some _v2 => d2 -- what is my comma doing all the way there
    | _       , _       => {data := none}


instance ConstantFold : EGraph.Analysis MathLang MathLangData where

  -- For Make, if constant lift to option. If add/mul/sub/div then check if children are const
  make := myMake

  join := myJoin

  modify eg id :=
    -- hold on a minute do we need destructive rewriting?
    let data := (eg.ecmap.get! id).data
    match data.data with
    | none => eg -- No constant known, do nothing
    | some n =>
        let addNew : EGraphM MathLang MathLangData Unit := do
          let constId ← push { head := MathLang.const n, args := [] } myMake
          --dbg_trace s!"AAAAA {constId}"
          --dbg_trace s!"AAAAAAAA {n}"
          let _ ← union id constId myJoin
          return ()

        let (_, eg') := addNew.run eg
        eg'

abbrev MathLangIO := EGraphGenericIO MathLang MathLangData

/-
  Helper Functions from math.rs
-/
/-
def isSym (en : ENode MathLang) : Bool :=
  match en.head with
  | .sym n => true
  | _      => false

def isConst (id : EClassId) : EGraphM MathLang MathLangData (Bool) := do
  let eg ← get
  let cid ← lookupCanonicalEClassId id
  let analysis := (eg.ecmap.get! cid).data
  match analysis.data with
  | some n => return true
  | none   => return false
-/

--TODO: clean up custom functions?
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

def isSym (var : String) : Dict MathLang → EGraphM MathLang MathLangData Bool :=
  λ dict => do
    let id := dict.get! var
    let cid ← lookupCanonicalEClassId id
    let eg ← get
    let ec := (eg.ecmap.get! cid)
    /-
    for en in ec.nodes do
      match en.head with
      | .sym _ => return true
      | _      => ()
    return false
    -/
    return ec.nodes.any (λen => match en.head with | .sym _ => true | _ => false) -- apparently the newline is not necessary who knew

def isConstOrDistinctVar (c x : String) : Dict MathLang → EGraphM MathLang MathLangData Bool :=
  λ dict => do
    let idC := dict.get! c
    let idX := dict.get! x
    let cidC ← lookupCanonicalEClassId idC
    let cidX ← lookupCanonicalEClassId idX

    -- Is distinct var?
    if cidC != cidX then
      return true
    -- Is const?
    else
      let eg ← get
      let analysis := (eg.ecmap.get! cidC).data
      match analysis.data with
      | some _ => return true -- is const.
      | none   => return false -- is neither const nor distinct

abbrev MathRule := Rule MathLang MathLangData


prefix:100 "?" => Pattern.PatVar

-- 2. The Rules
def mathRules : List (MathRule) := [

  r* pAdd (?"a") (?"b") === pAdd (?"b") (?"a"),
  r* pMul (?"a") (?"b") === pMul (?"b") (?"a"),
  r* pAdd (?"a") (pAdd (?"b") (?"c")) === pAdd (pAdd (?"a") (?"b")) (?"c"),
  r* pMul (?"a") (pMul (?"b") (?"c")) === pMul (pMul (?"a") (?"b")) (?"c"),

  r* pSub (?"a") (?"b") === pAdd (?"a") (pMul (pConst (-1)) (?"b")),
  r* pDiv (?"a") (?"b") === pMul (?"a") (pPow (?"b") (pConst (-1))) if isNotZero "b",

  r* pAdd (?"a") (pConst 0) === (?"a"),
  r* pMul (?"a") (pConst 0) === (pConst 0),
  r* pMul (?"a") (pConst 1) === (?"a"),

  r* (?"a") === pAdd (?"a") (pConst 0),
  r* (?"a") === pMul (?"a") (pConst 1),

  r* pSub (?"a") (?"a") === (pConst 0),
  r* pDiv (?"a") (?"a") === (pConst 1),

  r* pMul (?"a") (pAdd (?"b") (?"c")) === pAdd (pMul (?"a") (?"b")) (pMul (?"a") (?"c")),
  r* pAdd (pMul (?"a") (?"b")) (pMul (?"a") (?"c")) === pMul (?"a") (pAdd (?"b") (?"c")),

  r* pMul (pPow (?"a") (?"b")) (pPow (?"a") (?"c")) === pPow (?"a") (pAdd (?"b") (?"c")),
  r* pPow (?"x") (pConst 0) === (pConst 1) if (isNotZero "x"),
  r* pPow (?"x") (pConst 1) === (?"x"),
  r* pPow (?"x") (pConst 2) === pMul (?"x") (?"x"),
  r* pPow (?"x") (pConst (-1)) === pDiv (pConst 1) (?"x") if isNotZero "x",
  r* pMul (?"x") (pDiv (pConst 1) (?"x")) === (pConst 1) if isNotZero "x",

  r* pDiff (?"x") (?"x") === (pConst 1) if isSym "x",
  r* pDiff (?"c") (?"x") === (pConst 0) if isConstOrDistinctVar "c" "x",

  r* pDiff (pAdd (?"a") (?"b")) (?"x") === pAdd (pDiff (?"a") (?"x")) (pDiff (?"b") (?"x")),
  r* pDiff (pMul (?"a") (?"b")) (?"x") === pAdd (pMul (?"a") (pDiff (?"b") (?"x"))) (pMul (?"b") (pDiff (?"a") (?"x"))),

  r* pDiff (pSin (?"x")) (?"x") === pCos (?"x"),
  r* pDiff (pCos (?"x")) (?"x") === pMul (pConst (-1)) (pSin (?"x")),

  r* pDiff (pLn (?"x")) (?"x") === pDiv (pConst 1) (?"x") if isNotZero "x",

  r* pDiff (pPow (?"f") (?"g")) (?"x") ===
     pMul (pPow (?"f") (?"g"))
          (pAdd (pMul (pDiff (?"f") (?"x")) (pDiv (?"g") (?"f")))
                (pMul (pDiff (?"g") (?"x")) (pLn (?"f")))) ifMultiple
                [
                  (isNotZero "f"), (isNotZero "g")
                ],


  r* pIntg (pConst 1) (?"x") === (?"x"),

  r* pIntg (pPow (?"x") (?"c")) (?"x") ===
     pDiv (pPow (?"x") (pAdd (?"c") (pConst 1))) (pAdd (?"c") (pConst 1)) if isConst "c",
  r* pIntg (pCos (?"x")) (?"x") === pSin (?"x"),
  r* pIntg (pSin (?"x")) (?"x") === pMul (pConst (-1)) (pCos (?"x")),
  r* pIntg (pAdd (?"f") (?"g")) (?"x") === pAdd (pIntg (?"f") (?"x")) (pIntg (?"g") (?"x")),
  r* pIntg (pSub (?"f") (?"g")) (?"x") === pSub (pIntg (?"f") (?"x")) (pIntg (?"g") (?"x")),
  r* pIntg (pMul (?"a") (?"b")) (?"x") ===
     pSub (pMul (?"a") (pIntg (?"b") (?"x")))
          (pIntg (pMul (pDiff (?"a") (?"x")) (pIntg (?"b") (?"x"))) (?"x"))
]
