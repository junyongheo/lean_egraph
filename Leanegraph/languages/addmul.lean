import Leanegraph.framework
import Leanegraph.core

/-
  We define a language for basic tests on the e-graph.
  We further define a ToString instance for better debug/print-ability.
  The EGraph is bundled together with IO in a StateT
  ~~TODO: understand why IO can be passed as a state...~~
-/

open EGraph

inductive AddMul where
| lit   : Nat → AddMul
| var   : String → AddMul
| add   : AddMul
| mul   : AddMul
deriving DecidableEq, Hashable, Repr

instance : ToString AddMul where
  toString
  | .lit n => s!"{n}"
  | .var s   => s
  | .add     => "+"
  | .mul     => "*"

instance Analysis : EGraph.Analysis AddMul Unit where
  make    _  _ := ()
  join    _  _ := ()
  modify  eg _ := eg

/-
  Pass your language like so
-/
abbrev EGraphIO := EGraphGenericIO AddMul Unit


instance : ParseExpr AddMul where
  parse sx :=
  match sx with
  | .atom s =>
    match s.toNat? with
    | some n => some (.lit n, [])
    | none   => some (.var s, [])
  | .list (head :: args) =>
    match head with
    | .atom "+"    => some (.add,  args)
    | .atom "*"    => some (.mul,  args)
    | _ => none
  | .list [] => none


def liftVar (s : String) : Pattern AddMul := Pattern.PatVar s
def liftTerm (h : AddMul) (args : List (Pattern AddMul)) : Pattern AddMul := Pattern.PatTerm h (Array.mk args)

def pAdd  (x y : Pattern AddMul ) := liftTerm (.add    ) [x, y]
def pMul  (x y : Pattern AddMul ) := liftTerm (.mul    ) [x, y]
def pLit  (n : Nat              ) := liftTerm (.lit n  ) []
def pVar  (s : String           ) := liftTerm (.var s  ) []



structure AddMulData where
  data : Option Nat

instance : Inhabited (AddMulData) where
  default := {
    data := none
  }

def myMake (en : ENode AddMul) (children : Array AddMulData) : AddMulData :=
  -- Safe access for the analysis value
  let x := if children.isEmpty then
              (λ _ => none)
            else
              ((λ i => (children[i]!).data) : (Nat → Option Nat))
  -- If a constant, lift to data
  -- If an operation and both operands have a constant, calculate the value
  match en.head, en.args with
  | AddMul.lit n, _ => {data := some n}
  | .add, _     =>
    match x 0, x 1 with
    | some a, some b => {data := some (a + b)}
    | _     , _      => {data := none}
  | .mul, _     =>
    match x 0, x 1 with
    | some a, some b => {data := some (a * b)}
    | _     , _      => {data := none}
  | _, _        => {data := none}


  def myJoin (d1 : AddMulData) (d2 : AddMulData) : AddMulData :=
    match d1.data, d2.data with
    | some v1 , some v2 => if (v1 = v2) then d1 else (panic! s!"Constant Join fail, {v1} ≠ {v2}")
    | some _v1, _       => d1
    | _,       some _v2 => d2
    | _       , _       => {data := none}


instance ConstantFold : EGraph.Analysis AddMul AddMulData where

  make := myMake

  join := myJoin

  modify eg id :=
    let data := (eg.ecmap.get! id).data
    match data.data with
    | none => eg
    | some n =>
        let addNew : EGraphM AddMul AddMulData Unit := do
          let constId ← pushAnalysis (.lit n) myMake
          let _ ← union id constId myJoin
          return ()

        let (_, eg') := addNew.run eg
        eg'

abbrev AddMulIO := EGraphGenericIO AddMul AddMulData
