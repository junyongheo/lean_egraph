import Batteries.Data.UnionFind
import Leanegraph.core.TypeClass

open EGraphOps

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]

variable [EGOps : EGraphOps α ArgType NodesType ParentsType EGraph ECMap HCType ECMType DirtyType]

def repair (id : EClassId) : StateM EGraph Unit := do
  let canonId ← EGOps.lookupCanonicalEClassId id
  let eg ← get
  let some eClass := EGOps.lookupECMap? (EGOps.getECMap eg) canonId
    | return ()

  -- Loop 1...
  let (updateHCons, collisions) ← EGOps.foldlMParents (λ (hcons', collisions') (p : (_ × EClassId)) => do -- _ is ENode α...
      let canon ← EGOps.canonicalise p.1
      let canonId ← EGOps.lookupCanonicalEClassId p.2
      let det := EGOps.eraseHCons hcons' p.1
      match EGOps.lookupHCons? det canon with
      | some key => return (det, (canonId, key) :: collisions') -- keeps track of things to merge without collisions
      | none     => return (EGOps.insertHCons det canon canonId, collisions')
  ) (init := (EGOps.getHCons eg, [])) (target := EGOps.getParents eClass)

  let eg ← get
  let _ ← set <| EGOps.setHCons eg updateHCons -- make this monadic?

  for (id₁, id₂) in collisions do
    let _ ← EGOps.union id₁ id₂

  --let curNodes ← eClass.nodes.mapM canonicalise
  let curNodes ← EGOps.mapMNodes EGOps.canonicalise (EGOps.getNodes eClass)
  let newNodes := EGOps.dedupNodes curNodes

  -- Loop 2...
  let (_, newParents) ← EGOps.foldlMParents (target := EGOps.getParents eClass) (init := (EGOps.makeEmptyHCons, EGOps.makeEmptyParents)) (λ (hca, parents') (p : (_ × EClassId)) => do
    let canon ← EGOps.canonicalise p.1
    let canonId ← EGOps.lookupCanonicalEClassId p.2
    match EGOps.lookupHCons? hca canon with
    | some eid =>
      let _ ← EGOps.union eid canonId
      return (hca, parents')
    | none    =>
      return (EGOps.insertHCons hca canon canonId, EGOps.insertParent parents' canon canonId)
  )
  let eg' ← get
  let canonId' ←  (EGOps.lookupCanonicalEClassId canonId)
  let some eClassFinal := EGOps.lookupECMap? (EGOps.getECMap eg') canonId'
    | return ()
  -- eg'.ecmap.get! canonId' -- needs to be canonicalised again

  let eClassFinal' := EGOps.setNodes (EGOps.setParents eClassFinal newParents) newNodes
  let _ ← set (EGOps.setECMap eg' (EGOps.insertECMap (EGOps.getECMap eg') canonId' eClassFinal'))


/-
Haskell Egg...
Takes e-graph, returns egraph. We can just use a state monad so change to StateM EGraph (Unit)

rebuild :: (Analysis a l, Language l) => EGraph a l -> EGraph a l
rebuild (EGraph uf cls mm wl awl) =
  -- empty worklists
  -- repair deduplicated e-classes
  let
    -- erase
    emptiedEgr = EGraph uf cls mm mempty mempty

    wl'   = nubOrd $ bimap (`find` emptiedEgr) (`canonicalize` emptiedEgr) <$> wl
    egr'  = foldr repair emptiedEgr wl'

    awl'  = nubIntOn fst $ first (`find` egr') <$> awl
    egr'' = foldr repairAnal egr' awl'
  in
  -- Loop until worklist is completely empty
  if null (worklist egr'') && null (analysisWorklist egr'')
     then egr''
     else rebuild egr'' -- ROMES:TODO: Doesn't seem to be needed at all in the testsuite.
{-# INLINEABLE rebuild #-}

-/
