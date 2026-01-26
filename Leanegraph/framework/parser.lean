import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String
/-
  Note: https://lean-lang.org/doc/reference/latest/releases/v4.12.0/
  Has Parsec moved, so I hope this doesn't cause any more breaking changes in the future?
  Seemed easier than writing my own parser
  Zulip does say it's going to go poof, so find a better sol...
  https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Internal.2EParsec.2EString.2EParser/with/547253305
-/

/-
  Note: Notes:
  If error, check for mistakes in understanding.

  "skip" => consume a token/character.
  To be specific: Since we use "peek?", we already have
  the next character written down so "skip" just consumes that one.
  Realistically, we do NOT skip the character without any sign.

  "ws" => consumes all whitespace. Trust that it works...

  References:
  lean4/src/Lean/Data(Json/XML/Parser.lean)
  https://lean-lang.org/doc/api/Std/Internal/Parsec/Basic.html

  Let's hope we don't have to come back here
-/

namespace ExprParser

inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr
  deriving Repr


/-

/-
  Doesn't work because recursively defined..? Which.. I thought should work? TODO: why?
-/
instance : ToString SExpr where
  toString
  | .atom s => s
  | .list l => "( " ++ ((l.map toString).foldl (init := "") (λ cur str => cur ++ str) ) ++  " )"
-/

def stringToSExpr (sx : SExpr) : String :=

  match sx with
  | SExpr.atom s => /-dbg_trace s!"ATOM OF {s}" ;-/s ++ " "
  | SExpr.list l => "(" ++ ((l.map stringToSExpr).foldl (init := " ") (λ cur str => cur ++  str) ) ++  ")"
  -- | SExpr.list l => ((l.map stringToSExpr).foldl (init := "") (λ cur str => cur ++ " " ++  str) ) --for debug read

instance : ToString SExpr where
  toString := stringToSExpr


partial def SExprParser : Parser SExpr := do
  let c ← peek?
  --dbg_trace s!"At {c}"
  match c with
  | some '(' =>
    skip
    ws
    let items ← many SExprParser
    --dbg_trace s!"Items : {items}"
    --dbg_trace s!"Ate all WS"
    let _ ← pstring ")"
    ws
    --dbg_trace s!"Returning {items}"
    return SExpr.list items.toList
  | some _ =>
    let s ← many1Chars (satisfy fun c => !c.isWhitespace && c != '(' && c != ')')
    ws
    return SExpr.atom s
  | none => fail "Unexpected End of Input"



def parse (input : String) : Except String SExpr := do
  match SExprParser.run input with
  | .ok res => .ok res
  | .error e => .error s!"Error: {e}" -- is it better to preface with error?

def tests : IO Unit := do
  let tests := [
  "(+  1            2)",
  "(d x (ln x)       )",
  "(+ (* (2) (x)) (- y 5))",
  "(fancy(word))",
  "(   fancier   (   strings   )   )",
  "", -- fails on empty
  "+ 1 2", -- does need parenthesis
  "( + 1 2)",
  "( + 1 2 )))))))", -- accepts mismatched closing brackets
  "(((( + 1 2 )", -- does not accept mismatched opening brackets
  "()" -- empty paren is ok
  ]

  for t in tests do
    match parse t with
    | .ok res => IO.println s!"Parsed: {res}"
    | .error e => IO.println s!"{e}"

-- #eval tests
