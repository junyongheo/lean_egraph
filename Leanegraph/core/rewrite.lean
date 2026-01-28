import Leanegraph.core.egraphs

variable {α : Type _} [DecidableEq α] [Hashable α]
variable {D : Type _} [Inhabited D]

namespace EGraph

/-
  Define Pattern type
  Modelled after hegg (haskell)
  ```
    data Pattern lang
      = NonVariablePattern (lang (Pattern lang))
      | VariablePattern String
  ```
  and philip zucker's julia
  ```3
    struct PatVar
      id::Symbol
    end

    struct PatTerm
        head::Symbol
        args::Array{Union{PatTerm, PatVar}}
    end

    Pattern = Union{PatTerm,PatVar}
  ```
  I think this should work...
-/

-- https://proofassistants.stackexchange.com/questions/2444/does-lean-4-have-built-in-dictionary-types
abbrev Dict α [DecidableEq α] [Hashable α] := Std.HashMap /-(Pattern α)-/ String EClassId


inductive Pattern (α : Type _) where
| PatTerm : (head : α) → (args : Array <| Pattern α) → Pattern α
| PatVar : String → Pattern α
deriving Repr, Hashable --why decideableeq not work, look into


inductive Condition (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
| Equal        : Pattern α → Pattern α           → Condition α D
| NotEqual     : Pattern α → Pattern α           → Condition α D
| CustomLookup : (Dict   α → EGraphM α D (Bool)) → Condition α D
-- deriving Repr


-- https://unreasonableeffectiveness.com/learning-lean-4-as-a-programming-language-4-proofs/
-- https://unreasonableeffectiveness.com/learning-lean-4-as-a-programming-language-2-infinite-lists/
-- Some things on laziness and lists...

structure Rule (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
  lhs : Pattern α
  rhs : Pattern α
  cnd : Array (Condition α D) := Array.empty
-- deriving Repr -- I don't think other derivations required




mutual
partial def ematchlist (pl : Array (Pattern α)) (idl : Array EClassId) (idx : Nat) (d : Dict α) [Inhabited (Pattern α)] : EGraphM α D (Array (Dict α)) := do
  if _lastIndex : idx = pl.size then
    return if idx = idl.size then #[d] else #[]
  else if _stillValidIdx : idx < pl.size ∧ idx < idl.size then
    let p  := pl[idx] -- does lean get the proofs himself?
    let id := idl[idx] -- same here
    let canonId ← lookupCanonicalEClassId id
    let headMatches ← ematch p canonId d
    headMatches.flatMapM (λ d' =>
      ematchlist pl idl (idx+1) d'
    )
  else
    return #[]




partial def ematch (p : Pattern α) (id : EClassId) (d : Dict α) [Inhabited (Pattern α)] : EGraphM α D <| Array <| Dict α := do
  let canonId ← lookupCanonicalEClassId id
  match p with
  | Pattern.PatVar var =>
    match d.get? var with
    -- do key and id hold canonical ids? TODO: think... -- answer was no
    | some key => if key = canonId then return #[d] else return #[]
    | none     => return #[d.insert var canonId]
  | Pattern.PatTerm phead pargs =>
    let eg ← get
    match eg.ecmap.get? canonId with
    | none      => return #[]
    | some ecls =>
      let matchingNodes := ecls.nodes.filter (λ n => n.head == phead)
      let nestedMatches ← matchingNodes.flatMapM (λ enode =>
        ematchlist pargs enode.args 0 d
      )
      return nestedMatches
end

/-
mutual
def ematchlist (eg : EGraph α) (pl : List <| Pattern α) (idl : List EClassId) (d : Dict α) : List <| Dict α :=
  match pl with
  | [] => [d]
  | p :: ps =>
    ematch eg p idl.head! d |>.flatMap (λ d' =>
      ematchlist eg ps idl.tail! d'
    )


def ematch (eg : EGraph α) (p : Pattern α) (id : EClassId) (d : Dict α) : (List <| Dict α) :=
  match p with
  | Pattern.PatVar var =>
    match d.get? var with
    -- do key and id hold canonical ids? TODO: think...
    | some key => if key = id then [d] else []
    | none     => [d.insert var id]
  | Pattern.PatTerm phead pargs =>
    match eg.ecmap.get? id with
    | none      => []
    | some ecls =>
      ecls.nodes.flatMap (λ enode =>
        if enode.head ≠ phead then
          []
        else
          ematchlist eg pargs enode.args d
      )

end
-/

def instantiate [Analysis α D] (p : Pattern α) (d : Dict α) : EGraphM α D <| EClassId := do
  match p with
  | Pattern.PatVar var => return d.get! var
  | Pattern.PatTerm phead pargs =>
    -- push ⟨phead, List.map (λ a => instantiate a d) pargs⟩ -- maybe do this in multiple steps -- and in a monadmap
    let newArgs ← pargs.mapM (λ a => instantiate a d)
    push ⟨phead, newArgs⟩ Analysis.make
    -- push ⟨phead, ← pargs.mapM (λ a ↦ instantiate a d)⟩ -- can be done in one step like this
    -- still keep the two line definition for readability

def checkCondition [Analysis α D] (c : Condition α D) (d : Dict α) : EGraphM α D <| Bool := do
  match c with
  | Condition.Equal p1 p2 =>
    let id₁ ← lookupCanonicalEClassId (← instantiate p1 d)
    let id₂ ← lookupCanonicalEClassId (← instantiate p2 d)
    return id₁ = id₂
  | Condition.NotEqual p1 p2 =>
    let id₁ ← lookupCanonicalEClassId (← instantiate p1 d)
    let id₂ ← lookupCanonicalEClassId (← instantiate p2 d)
    return id₁ ≠ id₂
  | Condition.CustomLookup fn =>
    let b ← fn d
    return b


def rewrite {α : Type _} {D : Type _} [DecidableEq α] [Hashable α] [analysis : Analysis α D] [Inhabited D] [Inhabited (Pattern α)] (r : Rule α D) : EGraphM α D <| Unit := do
  let eg ← get

  let searchOp : List EClassId :=
    match r.lhs with
    | Pattern.PatTerm head _ =>
        (eg.opmap.getD head #[]).toList
    | Pattern.PatVar _ =>
        eg.ecmap.toList.map Prod.fst

  let pMatches : List (EClassId × Dict α) ← searchOp.flatMapM (λ id => do
      let subs ← (ematch r.lhs (← lookupCanonicalEClassId id) Std.HashMap.emptyWithCapacity)
      return (subs.map (λ sub => (id, sub))).toList)

  let condTrue ← pMatches.filterM (λ (_, d) => do
    r.cnd.allM (λc => checkCondition c d)

  )

  let joinFn := Analysis.join (α := α) (D := D)

  condTrue.forM (λ (lhsId, sub) => do
    let rhsId ← instantiate r.rhs sub
    let _     ← union lhsId rhsId joinFn
  )


  -- rebuild




end EGraph

/-
  function instantiate(e::EGraph, p::PatTerm , sub)
    push!( e, Term(p.head, [ instantiate(e,a,sub) for a in p.args ] ))
end
-/

/-
-- Oh great more monads
def ematch (p : Pattern α) (id : EClassId) (d : Dict α) : EGraphM α D (List <| Dict α) := do
  let eg ← get
  match p with
  | Pattern.PatVar var =>
    match d.get? var with
    -- do key and id hold canonical ids? TODO: think...
    | some key => if key = id then return [d] else return []
    | none     => return [d.insert var id]
  | Pattern.PatTerm phead pargs =>
    sorry
end
-/



/-
-- So apparently this is not part of the implementation O_o
-- It was a good thought exercise...

-- We want an option monad for option chaining reasons
-- Fold over a list of (key × val), I don't understand philip zucker's code tbh so I just translated it for now
-- TODO: read and understand what it says
-- We need to split the code into two parts, this does the inner loop (from for (k,v) in d)
def mergeConsistentHelper (carryOver ds : Dict α) : Option <| Dict α :=
  ds.toList.foldlM (init := carryOver)
  (λ hmp (k,v) =>
    match hmp.get? k with
    | some exs => if (exs = v) then some hmp else none
    | none     => some (hmp.insert k v)
  )

-- we need to ehm.. I think the code needs to be translated a bit
-- get the base case and proceed from there, otherwise termination is iffy?
def mergeConsistent (ds : List <| Option <| Dict α) : Option <| Dict α :=

  sorry

-- Can termination of this be checked?
def matchTo (en : ENode α) (p : Pattern α) : Option <| Dict α :=
  match p with
  | Pattern.PatVar var => some <| Std.HashMap.emptyWithCapacity |>.insert p en
  | Pattern.PatTerm phead pargs =>
    if phead ≠ en.head ∨ pargs.length ≠ en.args.length
      then none
    else
      List.zip en.args pargs
      -- mergeConsistent <| List.map matchTo
      sorry
    sorry

def matchRecursor (tup : (ENode α × Pattern α)) : Option <| Dict α :=
  match tup.snd with
  | Pattern.PatVar var => some <| Std.HashMap.emptyWithCapacity |>.insert tup.snd tup.fst
  | Pattern.PatTerm phead pargs =>
    if phead ≠ tup.fst.head ∨ pargs.length ≠ tup.fst.args.length
      then none
    else
      mergeConsistent <| List.map matchRecursor

#eval List.zip [1,2,3] ['a','b','c']



  --Std.HashMap.emptyWithCapacity |>.insert en p
-/
