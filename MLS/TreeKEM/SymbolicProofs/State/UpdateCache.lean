module

public import MLS.TreeKEM.SymbolicSpec.State.UpdateCache
public import MLS.TreeSync.SymbolicProofs.AuthService.CredentialInterpretation
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeKEM.SymbolicSpec.State.UpdateCache
import DY.Meta.Step

/-!
Port of the invariant and proofs of `MLS.TreeKEM.Symbolic.State.UpdateCache`.

Port-specific differences:
- The map predicate has no session identifier (see `DySlop.Map.MapPred`). It is an instance of `MapPred`,
  which gives the invariant of the maps: MLS*'s `has_update_cache_invariant` is not needed.
- The proofs of the traceful functions (`find_update_leaf_sk_proof`, `remember_update_leaf_sk_proof`)
  are DyLean Hoare triples (instances), assuming the proof trace entries of the map.
  The `tr_out == tr` part of their postconditions is not ported.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.TreeSync
open DySlop.Map (Map MapPred)

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (Map UpdateCacheKey UpdateCacheValue))]

/-- Port of `update_cache_pred`. -/
public
instance updateCachePred: MapPred UpdateCacheKey UpdateCacheValue where
  pred tr me key _ :=
    (LeafNode.mf tkt).wf (Bytes.Publishable · tr) key.leafNode ∧
    credentialToPrincipal key.leafNode.data.credential = some me
  pred_later tr1 tr2 prin key value := by
    grind
  pred_knowable tr prin key value m _ h := by
    show UpdateCacheKey.mf.wf _ _ ∧ UpdateCacheValue.mf.wf _ _
    rw [UpdateCacheKey.mf.wf_eq, UpdateCacheValue.mf.wf_eq]
    exact ⟨wf_knowableBy_of_publishable (LeafNode.mf tkt) (label prin m) tr key.leafNode h.1, trivial⟩

section Proofs

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map UpdateCacheKey UpdateCacheValue))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map UpdateCacheKey UpdateCacheValue))]

/-- Invariant of `initialize_update_cache` (DY*'s `initialize_map_invariant`). -/
@[instance]
public
theorem initializeUpdateCache.proof (prin: Participant):
  HoareTriple
    (initializeUpdateCache prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeUpdateCache
  exact DySlop.Map.initializeMap.proof prin

/-- Port of `find_update_leaf_sk_proof`. -/
@[instance]
public
theorem findUpdateLeafSk.proof (me: Participant) (sid: Nat) (leafNode: LeafNode Bytes tkt):
  HoareTriple
    (findUpdateLeafSk me sid leafNode)
    (fun _ => True)
    (fun _ _ => credentialToPrincipal leafNode.data.credential = some me)
:= by
  unfold findUpdateLeafSk
  step
  step
  simp only [MapPred.pred] at *
  grind

/-- Port of `remember_update_leaf_sk_proof`. -/
@[instance]
public
theorem rememberUpdateLeafSk.proof (me: Participant) (sid: Nat) (leafNode: LeafNode Bytes tkt) (leafSkSid: Nat):
  HoareTriple
    (rememberUpdateLeafSk me sid leafNode leafSkSid)
    (fun tr =>
      (LeafNode.mf tkt).wf (Bytes.Publishable · tr) leafNode ∧
      credentialToPrincipal leafNode.data.credential = some me
    )
    (fun _ _ => True)
:= by
  unfold rememberUpdateLeafSk
  exact DySlop.Map.addKeyValue.proof me sid _ _

end Proofs

end MLS.TreeKEM
