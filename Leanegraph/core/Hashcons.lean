import Leanegraph.core.SharedDefs

namespace Naive
/-
  Notes: HCons must always be canonical nodes for lookup purposes, scan code for that also TODO:
  Also that the UF always points to canonical values
  Also that the Hcons are unique
  Make them Prop s?
  Many things are unique keys, since they're maps
  Use hcons.insertUnique or something where I define it?
-/
/-
  Basic Union Find, to make it as simple as possible
  Goals: Reasoning...? Provability...? Not-break-my-head-ability? Pure?
  Should not be difficult to swap out later

  Some notes

  1. Every ID must have been pushed before use (doable)
  2. Uf.push must be the only way to add things in (is doable)
  3. Nothing must be removed, ever (see note 1)

  For 2, note that union only updates and doesn't add/remove classes
-/
abbrev UF := List <| EClassId × EClassId

def UF.find (uf : UF) (id : EClassId) : EClassId :=
  uf.lookup id |>.getD id

-- Leader is always id₁
def UF.union (uf : UF)  (id₁ id₂ : EClassId) : UF × EClassId:=
  let leader₁ := uf.find id₁
  let leader₂ := uf.find id₂
  if leader₁ == leader₂ then (uf, leader₁)
  else
  let newUf := uf.map (λ (member, leader) =>
    if leader == leader₂ then (member, leader₁) else (member, leader)
  )
  (newUf, leader₁)

def UF.size (uf : UF) : Nat :=
  uf.length

def UF.push (uf : UF) : UF × EClassId :=
  let newClass := uf.size
  ((newClass, newClass) :: uf, newClass)


-- #eval UF.union (UF.push ([] : UF) |>.1 |> UF.push |>.1 |> UF.push |>.1) 0 2 |>.1

def UF.isValidID (uf : UF) (id : EClassId) : Prop :=
  id < uf.size

-- because of this, changed def to abbrev
-- alternatively could define membership for uf but this seems easier?
-- TODO: abbrev vs def
def UF.pairCanon (uf : UF) : Prop :=
  ∀ id cid, (id, cid) ∈ uf → uf.find cid = cid



end Naive
