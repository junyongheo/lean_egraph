import Leanegraph.framework

/-
  We define a language for basic tests on the e-graph.
  We further define a ToString instance for better debug/print-ability.
  The EGraph is bundled together with IO in a StateT
  ~~TODO: understand why IO can be passed as a state...~~
-/
inductive AddMul where
| lit : Nat → AddMul
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
