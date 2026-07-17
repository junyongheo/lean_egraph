import Leanegraph.core.UnionFind
import Leanegraph.core.ListAsMaps
import Leanegraph.core.Naive
import Leanegraph.core.NaiveDefs
import Leanegraph.core.SharedDefs
import Leanegraph.core.MathlibJjajibgi

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

/-
  Helpers
-/
def inEClass (eg : EGraph α D) (en : ENode α) (id : EClassId) : Prop :=
  ∃ ecls, ecmapLookup eg id = some ecls ∧ en ∈ ecls.nodes


/-
  Represented
-/

mutual
/-
def nodeRepresentsTerm (eg : EGraph α D) (en : ENode α) (t : Term α) : Prop :=
  en.head = t.head ∧ Forall₂ (classRepresentsTerm eg) en.args t.args
-/
inductive nodeRepresentsTerm (eg : EGraph α D) : ENode α → Term α → Prop where
  | node :
      ∀ (en : ENode α) (t : Term α),
           en.head = t.head →
           Forall₂ (classRepresentsTerm eg) en.args t.args →
           nodeRepresentsTerm eg en t

inductive classRepresentsTerm (eg : EGraph α D) : EClassId → Term α → Prop where
  | cls :
      ∀ (id : EClassId) (t : Term α),
          (en : ENode α) →
          inEClass eg en id →
          nodeRepresentsTerm eg en t →
          classRepresentsTerm eg id t
end

def egraphRepresentsTerm (eg : EGraph α D) (t : Term α) : Prop :=
  ∃ id, classRepresentsTerm eg id t


/-
  Equivalences
-/

def EquivECId (eg : EGraph α D) (id₁ id₂ : EClassId) : Prop :=
  lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂

def EquivENode (eg : EGraph α D) (en₁ en₂ : ENode α) : Prop :=
  ∃ id, inEClass eg en₁ id ∧ inEClass eg en₂ id

def EquivTerm (eg : EGraph α D) (t₁ t₂ : Term α) : Prop :=
  ∃ (id : EClassId),
    classRepresentsTerm eg id t₁ ∧ classRepresentsTerm eg id t₂



def EquivENode' (eg : EGraph α D) (en₁ en₂ : ENode α) : Prop :=
  ∃ id₁ id₂,
    hcLookup eg (canonicalise eg en₁) = some id₁ ∧
    hcLookup eg (canonicalise eg en₂) = some id₂ ∧
    lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂





/-
  Props of E-Nodes
-/
-- An ENode is canonical if all arguments are canonical
def ENode.isCanonical (en : ENode α) (eg : EGraph α D) : Prop :=
  ∀ arg ∈ en.args, arg = lookupCanonicalEClassId eg arg
  -- en.args.map (lookupCanonicalEClassId eg) = en.args
  -- should be the same, figure out which one is better

-- Two ENodes are congruent if head is equal, all args are in same eclass ≅
def ENode.congrRel (eg : EGraph α D) (en₁ en₂ : ENode α)  : Prop :=
-- Is there a zip in lean?
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Forall2.html This is pretty cool
-- Oh it's mathlib
-- Back to zip
  -- en₁.head = en₂.head ∧ (en₁.args.zip en₂.args).all (λ (a, b) ↦ lookupCanonicalEClassId a = lookupCanonicalEClassId b)

  en₁.head = en₂.head ∧
    Forall₂ (λ a b => EquivECId eg a b) en₁.args en₂.args
  --en₁.args.length = en₂.args.length ∧
  --(en₁.args.zip en₂.args).all (λ (a, b) ↦ lookupCanonicalEClassId eg a = lookupCanonicalEClassId eg b)



-- EGraph Components
-- ecmap, hcons always unique keys if the functions defined in ListAsMaps.lean are used


/-
  Props about the EGraph State
-/
def EGraph.isClean (eg : EGraph α D) : Prop :=
  eg.dirty.isEmpty ∧ eg.aldrt.isEmpty

/-
  That the dirty and aldrt (analysis dirty) lists hold only valid IDs
-/
def EGraph.dirtyValid (eg : EGraph α D) : Prop :=
  ∀ id ∈ eg.dirty, eg.uf.isValidID id

def EGraph.aldrtValid (eg : EGraph α D) : Prop :=
  ∀ id ∈ eg.aldrt, eg.uf.isValidID id


-- Hashcons is correct when all enodes in it are canonical and the enodes point to a canonical id
-- Hashcons can be stale, between union and rebuild
def hashconsCanonical (eg : EGraph α D) : Prop :=
  ∀ en id, eg.hcons.lookup en = some id → en.isCanonical eg ∧ lookupCanonicalEClassId eg id = id


-- every valid entry in hcons is valid in the ecmap (when canon id)
-- does this hold between union and rebuild
-- connects the 3 parts of the egr
def EGraph.hconsToEcmap (eg : EGraph α D) : Prop :=
  ∀ en id, hcLookup eg en = some id →
    ∃ cls, ecmapLookup eg (lookupCanonicalEClassId eg id) = some cls


-- parents of entry in ecmap is all valid IDs
def EGraph.ecmapParentsValid (eg : EGraph α D) : Prop :=
  ∀ id cls, eg.ecmap.lookup id = some cls →
    ∀ p ∈ cls.parents, eg.uf.isValidID p.2

-- everything in hcons is all valid IDs
def EGraph.hconsValidity (eg : EGraph α D) : Prop :=
  ∀ node id, eg.hcons.lookup node = some id → eg.uf.isValidID id


-- Invariants that must always hold
def EGraph.alwaysInvariants (eg : EGraph α D) : Prop :=
  UF.wellFormed eg.uf ∧ -- all IDs are valid and is flat
  -- ecmap/hcons has unique keys, but that is from subtype, not mentioned here
  -- still keep that in mind, probably need
  eg.dirtyValid ∧
  eg.aldrtValid ∧
  eg.hconsToEcmap ∧
  -- i think this is about it?
  -- hcons can go stale, ecmap can go stale
  -- uf is i think always valid?
  -- added extra ones to show that the hcons and ecmap have valid ids
  eg.hconsValidity ∧
  eg.ecmapParentsValid

/-
  Congruence Closure

-- on node equivalence, we want a relation R (EquivENode), two ENodes (feed as args)
-- within the context of the egraph (feed as arg), which handles eclasses so
-- only EGraph → ENode → ENode → Prop?
--
  From egg (paraphrased): Congruence closure is the smallest superset of ≣node that is
  also the smallest superset of ≅
  To build congruence closure therefore we start with both of these as a base relation

-/

/-
  Try 1:
-/
/-
inductive CongruenceClosure (eg : EGraph α D) : ENode α → ENode α → Prop where
| equiv : (en₁ : ENode α) → (en₂ : ENode α) → EquivENode eg en₁ en₂ →
            CongruenceClosure eg en₁ en₂
| struc : (en₁ : ENode α) → (en₂ : ENode α) → ENode.congrRel eg en₁ en₂ →
            CongruenceClosure eg en₁ en₂
| refl  : (en  : ENode α) →
            CongruenceClosure eg en  en
| symm  : (en₁ : ENode α) → (en₂ : ENode α) → CongruenceClosure eg en₁ en₂ →
            CongruenceClosure eg en₂ en₁
| trans : (en₁ : ENode α) → (en₂ : ENode α) → (en₃ : ENode α) → CongruenceClosure eg en₁ en₂ → CongruenceClosure eg en₂ en₃ →
            CongruenceClosure eg en₁ en₃
-/
/-
  Try 2:
-/
inductive SingleStepOfCongruence (eg : EGraph α D) : ENode α → ENode α → Prop where
| equiv : (en₁ : ENode α) → (en₂ : ENode α) → EquivENode eg en₁ en₂ →
            SingleStepOfCongruence eg en₁ en₂
| struc : (en₁ : ENode α) → (en₂ : ENode α) → ENode.congrRel eg en₁ en₂ →
            SingleStepOfCongruence eg en₁ en₂


inductive CongruenceClosure (eg : EGraph α D) : ENode α → ENode α → Prop where
| refl  : (en          : ENode α) → CongruenceClosure eg en en
| symm  : (en₁ en₂     : ENode α) → CongruenceClosure eg en₁ en₂ → CongruenceClosure eg en₂ en₁
| trans : (en₁ en₂ en₃ : ENode α) → CongruenceClosure eg en₁ en₂ → SingleStepOfCongruence eg en₂ en₃ → CongruenceClosure eg en₁ en₃


/-
  Try 3:
-/
/-
inductive SingleStepOfCongruence' (eg : EGraph α D) : ENode α → ENode α → Prop where
| equiv : (en₁ : ENode α) → (en₂ : ENode α) → EquivENode eg en₁ en₂ →
            SingleStepOfCongruence' eg en₁ en₂
| struc : (en₁ : ENode α) → (en₂ : ENode α) → ENode.congrRel eg en₁ en₂ →
            SingleStepOfCongruence' eg en₁ en₂
-- | refl  : (en  : ENode α) → SingleStepOfCongruence' eg en en -- technically same as CC3.refl
| symm  : (en₁ : ENode α) → (en₂ : ENode α) → SingleStepOfCongruence' eg en₁ en₂ → SingleStepOfCongruence' eg en₂ en₁



inductive CongruenceClosure3 (eg : EGraph α D) : ENode α → ENode α → Prop where
| refl  : (en          : ENode α) → CongruenceClosure3 eg en  en
| chain : (en₁ en₂ en₃ : ENode α) → CongruenceClosure3 eg en₁ en₂ → SingleStepOfCongruence' eg en₂ en₃ → CongruenceClosure3 eg en₁ en₃
-/

/-
-- doesn't work as well as the above?
inductive CongruenceClosure (eg : EGraph α D) (en₁ : ENode α) (en₂ : ENode α) : Prop where
| equiv : EquivENode eg en₁ en₂        → CongruenceClosure eg en₁ en₂
| congr : ENode.isCongruent en₁ en₂ eg → CongruenceClosure eg en₁ en₂
| symm  : CongruenceClosure eg en₁ en₂ → CongruenceClosure eg en₂ en₁ -- doesn't work
-/
/-
  Define the two main invariants for E-Graphs.
  1. Congruence Invariant
    The e-graph must ensure that congruent e-nodes are in the same e-class

  2. Hashcons Invariant
    From Egg: e-node 𝑛∈𝑀[𝑎] ⇐⇒ 𝐻[canonicalize(𝑛)]=find(𝑎)
    The hashcons 𝐻 must map all canonical e-nodes to their e-class ids
    enode en is in eclass (ecmap id₁) IFF hashcons.lookup(en) = uf.find id

  Bonus: Some analysis invariant?
    ∀𝑐∈𝐺. 𝑑𝑐=Ûmake(𝑛) and modify(𝑐)=𝑐 (copied egg pg.13, idk how to type that, TODO: )
-/

/-
def EGraph.congruenceInvariant
    -- (eg : EGraph α D) (en₁ en₂ : ENode α) (id₁ id₂ : EClassId) : Prop := -- no need to specify
    (eg : EGraph α D) : Prop :=
      ∀ en₁ en₂ id₁ id₂, -- forall en/id ₁₂ where
        eg.hcons.lookup en₁ = some id₁ → -- id₁ is the canon class of en₁
        eg.hcons.lookup en₂ = some id₂ → -- and id₂ of en₂
        ENode.isCongruent en₁ en₂ eg →  -- and the two nodes are congruent
        lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂ -- the two nodes are in the same e-class
-/

def EGraph.congruenceInvariant (eg : EGraph α D) : Prop :=
  ∀ (en₁ en₂ : ENode α),
    EquivENode eg en₁ en₂ ↔ CongruenceClosure eg en₁ en₂

def EGraph.uniqueContained (eg : EGraph α D) : Prop :=
  ∀ (en : ENode α) (id₁ id₂ : EClassId),
    hcLookup eg en = some id₁ →
    hcLookup eg en = some id₂ →
    lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂


def EGraph.hashconsInvariant (eg : EGraph α D) : Prop :=
  ∀ (en : ENode α) (id : EClassId),
    -- e-node 𝑛∈𝑀[𝑎]
    inEClass eg en id
    ↔
    -- 𝐻[canonicalize(𝑛)]=find(𝑎)
    hcLookup eg (canonicalise eg en) = lookupCanonicalEClassId eg id
-- huh doesn't this imply the congruenceInvariant? In the ← direction?
-- TODO: go for this one first, I think?
