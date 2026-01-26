import Leanegraph.framework
import Leanegraph.core

inductive PropLang where
| bool : Bool → PropLang
| and  : PropLang
| or   : PropLang
| not  : PropLang
| impl : PropLang
| sym  : String → PropLang
deriving DecidableEq, Hashable, Repr

instance : ToString PropLang where
  toString
  | .bool b => s!"{b}"
  | .and    => "and"
  | .or     => "or"
  | .not    => "¬"
  | .impl   => "→"
  | .sym s  => s!"{s}"

instance Analysis : EGraph.Analysis PropLang Unit where
  make    _ _ := ()
  join    _ _ := ()
  modify eg _ := eg

abbrev PropIO := EGraphGenericIO PropLang Unit
