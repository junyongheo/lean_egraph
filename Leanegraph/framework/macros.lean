import Leanegraph.core
import Leanegraph.framework.extraction
import Leanegraph.framework.helpers
-- ehm does this work? i guess. is this efficient? probably not.
-- Can make macro for rewrite rules r* ( lhs === rhs )
-- TODO: probably read "metaprogramming in lean 4" and get smth nicer...


/-
macro "r*" lhs:term " === " rhs:term " if " cnd:term : term =>
    `({ lhs := $lhs, rhs := $rhs, cnd := [Condition.CustomLookup ($cnd)] })
-/

open EGraph

prefix:100 "?" => Pattern.PatVar

/-
macro "r*" lhs:term " === " rhs:term : term =>
  `({ lhs := $lhs, rhs := $rhs, cnd := [] })
-/
-- macro "?" lhs:term : term => `(liftVar $lhs)

-- syntax "?" str : term
syntax "r*" term " === " term                                   : term
syntax "r*" term " === " term " if "             term           : term
syntax "r*" term " === " term " ifEQ "           term "," term  : term
syntax "r*" term " === " term " ifMultiple " "[" term,* "]"     : term


macro_rules
-- | `(?$s:str) =>
--    `(liftVar $s)
| `(r* $lhs  ===  $rhs) =>
    `({ lhs := $lhs, rhs := $rhs, cnd := #[] })
| `(r* $lhs  ===  $rhs if $cnd) =>
    `({ lhs := $lhs, rhs := $rhs, cnd := #[Condition.CustomLookup $cnd] })
| `(r* $lhs  ===  $rhs ifEQ $cnd₁, $cnd₂) =>
    `({ lhs := $lhs, rhs := $rhs, cnd := #[Condition.Equal $cnd₁ $cnd₂] })
-- if this doesn't work come back here
-- https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html
| `(r* $lhs  ===  $rhs  ifMultiple  [ $[$cnds],* ] ) =>
    `({
        lhs := $lhs,
        rhs := $rhs,
        cnd := #[$[Condition.CustomLookup $cnds],*]
    })
| `(push $head) =>
    `(runLine <| pushRun { head := $head, args := #[] })
| `(push $head [$args,*]) =>
    `(runLine <| pushRun { head := $head, args := #[$args,*] })
| `(union $id1 $id2) =>
    `(runLine <| unionRun $id1 $id2)
| `(rebuild) =>
    `(runLineUnit <| rebuildRun)
| `(parseTerm $head) =>
    `(
        match (ExprParser.SExprParser.run $head) with
        | .ok expr => runLine <| buildEGFromSExprGeneric expr
        | .error e => panic! s!"Error with {e}"
    )
| `(parseTerm $head "error" $errormsg) =>
    `(
        match (ExprParser.SExprParser.run $head) with
        | .ok expr => runLine <| buildEGFromSExprGeneric expr
        | .error e => panic! s!"{$errormsg}: {e}"
    )
| `(checkEquivalent $lhs $rhs) =>
    `(runLine <| checkSameClass $lhs $rhs)
| `(checkNonEquivalent $lhs $rhs) =>
    `(runLine <| checkDiffClass $lhs $rhs)
| `(pushAnalysis $head $myMake) =>
    `(push {head := $head, args := #[]} $myMake)
| `(pushAnalysis $head [$args,*] $myMake) =>
    `(EGraph.push {head := $head, args := #[$args,*]} $myMake)
