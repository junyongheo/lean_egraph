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


instance : ParseExpr PropLang where
  parse sx := match sx with
  | .atom s =>
    if s == "true"
      then some (.bool true, [])
    else if s == "false"
      then some (.bool false, [])
    else
      some (.sym s, [])

  | .list (head :: args) =>
    match head with
    | .atom "&"  => some (.and, args)
    | .atom "|"   => some (.or,  args)
    | .atom "¬"  => some (.not, args)
    | .atom "→" => some (.impl, args)
    | _ => none
  | .list [] => none

open EGraph

def liftVar (s : String) : Pattern PropLang := Pattern.PatVar s
def liftTerm (h : PropLang) (args : List (Pattern PropLang)) : Pattern PropLang := Pattern.PatTerm h (Array.mk args)

-- maybe I went a little overboard with matching spacing
def pBool(b   : Bool               ) := liftTerm (.bool b) []
def pAnd (a b : Pattern <| PropLang) := liftTerm (.and   ) [a, b]
def pOr  (a b : Pattern <| PropLang) := liftTerm (.or    ) [a, b]
def pNot (a   : Pattern <| PropLang) := liftTerm (.not   ) [a]
def pImpl(a b : Pattern <| PropLang) := liftTerm (.impl  ) [a, b]
def pSym (s   : String             ) := liftTerm (.sym s ) []

instance : Inhabited (Pattern PropLang) := {
  default := Pattern.PatVar "_"
}
-- macro "?" lhs:term : term => `(liftVar $lhs)




abbrev PropData := Option Bool

def makeProp (en : ENode PropLang) (children : Array PropData) : PropData :=
  -- Helper to get child data safely
  let get (i : Nat) : Option Bool :=
    if h : i < children.size then children[i] else none

  match en.head with
  | .bool b => some b
  | .sym _  => none
  | .not    =>
    match get 0 with
    | some b => some (!b)
    | _ => none
  | .and    =>
    match get 0, get 1 with
    | some a, some b => some (a && b)
    | _, _ => none
  | .or     =>
    match get 0, get 1 with
    | some a, some b => some (a || b)
    | _, _ => none
  | .impl   =>
    match get 0, get 1 with
    | some a, some b => some ((!a) || b)
    | _, _ => none

def myMake (en : ENode PropLang) (children : Array PropData) : PropData :=
  -- dbg_trace s!"ENode {en.head} Has Children? {!children.isEmpty}"
  let x (i : Nat) :=
    if _ : i < children.size then children[i]! else none

    match en.head with
    | PropLang.bool n =>
      some n
    | PropLang.sym _ => none
    | .and    =>
      match x 0, x 1 with
      | some a, some b =>
        some (a && b)
      | _     , _      => none
    | .or     =>
      match x 0, x 1 with
      | some a, some b => some (a ∨ b)
      | _     , _      => none
    | .not     =>
      match x 0 with
      | some a => some (not a)
      | _   => none
    | .impl     =>
      match x 0, x 1 with
      | some a, some b =>
        some (!a || b)
      | _     , _      => none


def myJoin (d1 d2 : PropData) : PropData :=
  match d1, d2 with
  | some a, some b =>
      if a == b then some a
      else panic! s!"conflict...: {a} vs {b}"
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

instance PropAnalysis : EGraph.Analysis PropLang PropData where
  make := myMake
  join := myJoin
  modify eg id :=
    let data := (eg.ecmap.get! id).data
    match data with
    | none => eg
    | some b =>
        let addNew : EGraphM PropLang PropData Unit := do
           let constId ← push { head := .bool b, args := #[] } myMake
           let _ ← union id constId myJoin
           return ()

        let (_, eg') := addNew.run eg
        eg'






-- Make it cleaner by restructuring this as smallerSet ++ (distributive rules)
def propRules {D : Type _} : List (Rule PropLang D) := [
  -- Def Imply
  r* pImpl (?"a") (?"b") === pOr (pNot (?"a")) (?"b"),
  -- Imply Flip
  r* pOr (pNot (?"a")) (?"b") === pImpl (?"a") (?"b"),
  -- Double Neg
  r* pNot (pNot (?"a")) === (?"a"),
  -- Double Neg Flip
  r* ?"a" === pNot (pNot (?"a")), -- is the parenthesis necessary
  -- Assoc Or
  r* pOr (pOr (?"a") (?"b")) (?"c") === pOr (?"a") (pOr (?"b") (?"c")),
  -- Dist and Or
  r* pAnd (?"a") (pOr (?"b") (?"c")) === pOr (pAnd (?"a") (?"b")) (pAnd (?"a") (?"c")),
  -- Dist Or And
  r* pOr (?"a") (pAnd (?"b") (?"c")) === pAnd (pOr (?"a") (?"b")) (pOr (?"a") (?"c")),
  -- Commutativity
  r* pOr (?"a") (?"b")  === pOr (?"b") (?"a"),
  r* pAnd (?"a") (?"b") === pAnd (?"b") (?"a"),
  -- Lem
  r* pOr (?"a") (pNot (?"a")) === pBool true,
  -- Or True
  r* pOr (?"a") (pBool true) === pBool true,
  -- Or False
  r* pOr (?"a") (pBool false) === (?"a"),
  -- And true
  r* pAnd (?"a") (pBool true) === (?"a"),
  -- And false
  r* pAnd (?"a") (pBool false) === (pBool false),
  -- Contrapositive
  r* pImpl (?"a") (?"b") === pImpl (pNot (?"b")) (pNot (?"a")),
  -- Not True/False
  r* pNot (pBool true) === pBool false,
  r* pNot (pBool false) === pBool true,
]

-- No distributive rules because that absolutely murders my laptop
def smallerSet {D : Type _} : List (Rule PropLang D) := [
    -- Def Imply
  r* pImpl (?"a") (?"b") === pOr (pNot (?"a")) (?"b"),
  -- Imply Flip
  r* pOr (pNot (?"a")) (?"b") === pImpl (?"a") (?"b"),
  -- Double Neg Flip
  r* ?"a" === pNot (pNot (?"a")), -- is the parenthesis necessary
  -- Lem
  r* pOr (?"a") (pNot (?"a")) === pBool true,
  -- Commutativity
  r* pOr (?"a") (?"b")  === pOr (?"b") (?"a"),
  r* pAnd (?"a") (?"b") === pAnd (?"b") (?"a"),
    -- Or True
  r* pOr (?"a") (pBool true) === pBool true,
  -- Or False
  r* pOr (?"a") (pBool false) === (?"a"),
  -- And true
  r* pAnd (?"a") (pBool true) === (?"a"),
  -- And false
  r* pAnd (?"a") (pBool false) === (pBool false),
  -- Contrapositive
  r* pImpl (?"a") (?"b") === pImpl (pNot (?"b")) (pNot (?"a")),
  -- Not True/False
  r* pNot (pBool true) === pBool false,
  r* pNot (pBool false) === pBool true,
  -- lem_imply (see rust code)
  r* pAnd (pImpl (?"a") (?"b")) (pImpl (pNot (?"a")) (?"c")) === pOr (?"b") (?"c")

]


abbrev PropIO := EGraphGenericIO PropLang PropData
abbrev PropRule := Rule PropLang PropData



def checkSameClassTests (id1 id2 : EClassId) (test : String := "") : PropIO Unit := do
  let st ← get
  let (_,c1) := st.uf.find! id1
  let (_,c2) := st.uf.find! id2

  if c1 != c2 then
    IO.println s!" FAIL: {test}"
    IO.println s!" ID {id1} -> Class {c1}"
    IO.println s!" ID {id2} -> Class {c2}"
