import Leanegraph.framework.helpers

inductive PropLang where
| bool : Bool → PropLang
| and  : PropLang
| or   : PropLang
| not  : PropLang
| impl : PropLang
| sym  : String → PropLang
deriving DecidableEq, Hashable, BEq, Repr

instance : ToString PropLang where
  toString
  | .bool b => s!"{b}"
  | .and    => "and"
  | .or     => "or"
  | .not    => "¬"
  | .impl   => "→"
  | .sym s  => s!"{s}"

abbrev EGraphIO := EGraphGenericIO PropLang
