import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers


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


abbrev LambdaIO := EGraphGenericIO Lambda
