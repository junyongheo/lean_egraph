import Leanegraph.egraph

variable {α : Type _} [BEq α] [DecidableEq α] [Hashable α]

/-
  Define Pattern type
  Modelled after hegg (haskell)
  ```
    data Pattern lang
      = NonVariablePattern (lang (Pattern lang))
      | VariablePattern String
  ```
  and philip zucker's julia
  ```
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
inductive Pattern (α : Type _) where
| PatTerm : (head : α) → (args : Pattern α) → Pattern α
| PatVar : α → Pattern α
deriving Repr



def matchPattern (en : ENode α) (p : Pattern α) : Std.HashMap (ENode α) (Pattern α) :=
  Std.HashMap.emptyWithCapacity |>.insert en p
