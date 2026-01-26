import Leanegraph.core
import Leanegraph.framework.helpers
import Leanegraph.framework.extraction
-- ehm does this work? i guess. is this efficient? probably not.
-- Can make macro for rewrite rules r* ( lhs === rhs )
-- TODO: probably read "metaprogramming in lean 4" and get smth nicer...
/-
macro "r*" lhs:term " === " rhs:term : term =>
  `({ lhs := $lhs, rhs := $rhs })

macro "?" lhs:term : term => `(pVar $lhs)
-/

open EGraph


macro_rules
  | `(push $head) =>
      `(runLine <| pushRun { head := $head, args := [] })
  | `(push $head [$args,*]) =>
      `(runLine <| pushRun { head := $head, args := [$args,*] })
  | `(rebuild) =>
      `(runLineUnit <| rebuildRun)
