abbrev EClassId := Nat

structure genericENode (α : Type _) (ArgType : Type _) where
  head : α
  args : ArgType
deriving Hashable, Repr, DecidableEq

structure genericEClass (α : Type _) (NodesType : Type _) (ParentsType : Type _) where
  nodes : NodesType -- List (ENode α)
  parents : ParentsType -- List (ENode α × EClassId) or HashMap for the same kv
deriving Hashable, Repr, DecidableEq


/-

-- Ideally this would take the place of "Foldable/Traversable" with less issues
-- And would allow for code reuse for cleaner code

-- Un-ideally it allows for me to cry thinking about typeclasses

class FoldableIsh (Container : Type) (α : Type) where
  cmap              : (α → α) → Container → Container
  cmapM             : {m : Type → Type} → [Monad m] → (α → m α) → Container → m Container
  cfoldr {β : Type} : (α → β → β) → β → Container → β
  cdedup            : [BEq α] → [Hashable α] → Container → Container
-/


/-
  This is the version with all the types being Type and not Type → Type
-/
class EGraphOps
    (α : Type) -- Type of Term
    /-(ENode : Type)-/ (ArgType : Type _) -- ENode Types
    /-(EClass : Type)-/ (NodesType : Type _) (ParentsType : Type _) -- EClass Types
    (EGraph : Type _) (ECMap : Type _)  (HCType : Type _) (ECMType : Type _) (DirtyType : Type _) -- EGraph Types
    /-(Data : Type)-/ where

  ENode  : Type := genericENode α ArgType
  EClass : Type := genericEClass α NodesType ParentsType


  -- Needs to Implement
  /-
  -- Structures (the actual definitions)
  -- NO! We only need to lay out the required actions here, the exact types of the structures
  -- can be done by the user, as long as all of our actions are fulfilled
  ENode : α → Type
  EClass : α → D → Type
  EGraph : α → D → Type
  Analysis :  α → D → Type -- skip for now
  -/
  -- Actions on the structures

  -- ENode
  -- canonicalise (ENode : Type) : StateM EGraph ENode
  canonicalise : ENode → StateM EGraph ENode
  getArgs      : ENode → ArgType
  setArgs      : ENode → ArgType → ENode
  mapArgs      : (EClassId → EClassId) → ArgType → ArgType
  -- updateParents (ecmap : Std.HashMap EClassId (EClass)) (en : ENode) (eid : EClassId) : Std.HashMap EClassId (EClass)
  -- updateParents : ENode → EClassId → StateM EGraph Unit
  -- TODO: is this viable? modify in-state and not return, see if this is possible because
  -- it's different from the original
  -- TODO: removed updateParents from the typeclass, I think we can just make it a helper function
  -- because it's only used in a single function
  -- and it's difficult to unify the types, but for this particular function it doesn't need to be

  -- EClass

  makeEmptyEClass : EClass

  -- makeEClassFromNode : ENode → Data → EClass
  makeEClassFromNode : ENode → EClass
  -- in essence we could just implement this using makeempty + add

  -- mergeEClasses : EClass → EClass → (Data → Data) → EClass
  -- TODO: is this correct?
  -- forget about the analyses for now
  mergeEClasses : EClass → EClass → EClass

  getNodes : EClass → NodesType
  setNodes : EClass → NodesType → EClass
  getParents : EClass → ParentsType
  setParents : EClass → ParentsType → EClass

  -- EGraph
  getSize : EGraph → Nat

  egrEmpty : EGraph

  getHCons : EGraph → HCType
  setHCons : EGraph → HCType → EGraph -- or HCType → EGraph? no
  eraseHCons : HCType → ENode → HCType
  insertHCons : HCType → ENode → EClassId → HCType

  lookupHCons? : HCType → ENode → Option EClassId
  makeEmptyHCons : HCType


  getECMap : EGraph → ECMType
  setECMap : EGraph → ECMType → EGraph
  lookupECMap? : ECMType → EClassId → Option EClass
  insertECMap  : ECMType → EClassId → EClass → ECMType

  --hardcode or not??
  --no indexing needed, only maps and foldr
  --is map and foldr much faster in array than list?
  getDirty   : EGraph → DirtyType -- List (EClassId × ENode)
  -- setDirty   : EGraph → DirtyType -- List (EClassId × ENode) → EGraph
  dirtyEmpty : EGraph → Bool
  emptyDirty : EGraph → EGraph
  dedupDirty : DirtyType → DirtyType
  mapDirty   : (EClassId × ENode → EClassId × ENode) → DirtyType → DirtyType
  forMDirty  : DirtyType → (EClassId × ENode → StateM EGraph Unit) → StateM EGraph Unit
  findEmpty  : EGraph → EClassId → EClassId


  -- because you take the current egraph, replace the hcons, then return the new egraph
  -- TODO: how to integrate with the StateM?

  -- I think no OpMap in the naive version?
  --rebuildOpMap : StateM EGraph Unit

  -- TODO: join (analysis) was removed here
  -- repair : EClassId → StateM EGraph Unit

  -- TODO: technically rebuild is just the egraph itself
  -- that works on itself without any external input until it terminates
  -- question: how to prove termination?
  rebuild : StateM EGraph Unit


  push : ENode → StateM EGraph EClassId

  union : EClassId → EClassId → StateM EGraph EClassId

  lookupCanonicalEClassId : EClassId → StateM EGraph EClassId

  findClass : ENode → StateM EGraph (Option EClassId)

  -- Helpers
  --https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Init/Data/List/Control.lean#L232-L252
  foldlMParents : {s : Type} → (s → ENode × EClassId → StateM EGraph s)
                → (init : s) → (target : ParentsType) → StateM EGraph s
  mapMNodes     : (ENode → StateM EGraph ENode) → NodesType → StateM EGraph NodesType
  dedupNodes    : NodesType → NodesType
  makeEmptyParents : ParentsType
  insertParent  : ParentsType → ENode → EClassId → ParentsType






/-
/-
  This is the version with everything being Type → Type
-/

class EGraphOps
    (α : Type) -- Type of Term
    /-(ENode : Type)-/ (ArgType : Type _ → Type _) -- ENode Types
    /-(EClass : Type)-/ (NodesType : Type _ → Type _) (ParentsType : Type _ → Type _) -- EClass Types
    (EGraph : Type _) (ECMap : Type _)  (HCType : Type _) (ECMType : Type _)-- EGraph Types
    /-(Data : Type)-/
    where


  ENode  : Type := genericENode α (ArgType EClassId)
  EClass : Type := genericEClass α (NodesType ENode) (ParentsType (ENode × EClassId))

  NodeArgs : Type := ArgType EClassId
  ClassNodes : Type := NodesType ENode
  ClassParents : Type := ParentsType (ENode × EClassId)

  -- Needs to Implement
  /-
  -- Structures (the actual definitions)
  -- NO! We only need to lay out the required actions here, the exact types of the structures
  -- can be done by the user, as long as all of our actions are fulfilled
  ENode : α → Type
  EClass : α → D → Type
  EGraph : α → D → Type
  Analysis :  α → D → Type -- skip for now
  -/
  -- Actions on the structures

  -- ENode
  -- canonicalise (ENode : Type) : StateM EGraph ENode
  canonicalise : ENode → StateM EGraph ENode
  -- updateParents (ecmap : Std.HashMap EClassId (EClass)) (en : ENode) (eid : EClassId) : Std.HashMap EClassId (EClass)
  -- updateParents : ENode → EClassId → StateM EGraph Unit
  -- TODO: is this viable? modify in-state and not return, see if this is possible because
  -- it's different from the original
  -- TODO: removed updateParents from the typeclass, I think we can just make it a helper function
  -- because it's only used in a single function
  -- and it's difficult to unify the types, but for this particular function it doesn't need to be

  -- EClass

  makeEmptyEClass : EClass

  -- makeEClassFromNode : ENode → Data → EClass
  makeEClassFromNode : ENode → EClass
  -- in essence we could just implement this using makeempty + add

  -- mergeEClasses : EClass → EClass → (Data → Data) → EClass
  -- TODO: is this correct?
  -- forget about the analyses for now
  mergeEClasses : EClass → EClass → EClass

  getNodes : EClass → NodeArgs
  setNodes : EClass → NodeArgs → EClass
  getParents : EClass → ClassParents
  setParents : EClass → ClassParents → EClass

  -- EGraph
  getSize : EGraph → Nat

  egrEmpty : EGraph

  getHCons : EGraph → HCType
  setHCons : EGraph → HCType → EGraph -- or HCType → EGraph? no
  eraseHCons : HCType → ENode → HCType
  insertHCons : HCType → ENode → EClassId → HCType

  getECMap : EGraph → ECMType
  setECMap : EGraph → ECMType → EGraph
  lookupECMap? : ECMType → EClassId → Option EClass
  insertECMap  : ECMType → EClassId → EClass → ECMType

  -- because you take the current egraph, replace the hcons, then return the new egraph
  -- TODO: how to integrate with the StateM?

  -- I think no OpMap in the naive version?
  --rebuildOpMap : StateM EGraph Unit

  -- TODO: join (analysis) was removed here
  -- repair : EClassId → StateM EGraph Unit

  -- TODO: technically rebuild is just the egraph itself
  -- that works on itself without any external input until it terminates
  -- question: how to prove termination?
  rebuild : StateM EGraph Unit


  push : ENode → StateM EGraph EClassId

  union : EClassId → EClassId → StateM EGraph EClassId

  lookupCanonicalEClassId : EClassId → StateM EGraph EClassId

  findClass : ENode → StateM EGraph (Option EClassId)

  -- Helpers
-/
