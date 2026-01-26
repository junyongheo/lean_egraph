import Leanegraph.framework

inductive Lambda where
| bool : Bool → Lambda
| num  : Int → Lambda
| var  : String → Lambda
| add  : Lambda
| eq   : Lambda
| app  : Lambda
| lam  : Lambda
| let_ : Lambda
| fix  : Lambda
| if_  : Lambda
deriving DecidableEq, Hashable, BEq, Repr

instance : ToString Lambda where
  toString
  | .bool b => s!"{b}"
  | .num n  => s!"{n}"
  | .var s  => s
  | .add    => "+"
  | .eq     => "="
  | .app    => "app"
  | .lam    => "lam"
  | .let_   => "let"
  | .fix    => "fix"
  | .if_    => "if"

abbrev NOA_LAMBD := Unit

instance Analysis_LAMBDA : EGraph.Analysis Lambda NOA_LAMBD where
  make    _ _ := ()
  join    _ _ := ()
  modify eg _ := eg

abbrev LambdaIO := EGraphGenericIO Lambda NOA_LAMBD
