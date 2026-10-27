module

public import MLS.TreeKEM.SymbolicSpec.State.PSKStore
public import MLS.TreeKEM.SymbolicProofs.State.OnePSKStore
public import MLS.TreeKEM.SymbolicProofs.PSK
public import MLS.Bootstrap.SymbolicProofs.Welcome
import all MLS.TreeKEM.SymbolicSpec.State.PSKStore
import DY.Meta.Step

/-!
Port of the invariant and proofs of `MLS.TreeKEM.Symbolic.State.PSKStore`.

Port-specific differences:
- The map predicate has no session identifier (see `DySlop.Map.MapPred`). It is an instance of `MapPred`,
  which gives the invariant of the maps: MLS*'s `has_psk_store_invariant` is not needed.
- The proofs of the traceful functions (`retrieve_psks_proof`, `remember_psk_proof`) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the states. The `tr_out == tr` part of their postconditions is not ported.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.Bootstrap
open DySlop.Map (Map MapPred)

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (Map PskStoreKey PskStoreValue))]

/-- Port of `psk_store_pred`. -/
public
instance pskStorePred: MapPred PskStoreKey PskStoreValue where
  pred tr _ key _ := PreSharedKeyIdShort.mf.wf (Bytes.Publishable · tr) key.pskId
  pred_later tr1 tr2 prin key value := by
    grind
  pred_knowable tr prin key value m _ h := by
    show PskStoreKey.mf.wf _ _ ∧ PskStoreValue.mf.wf _ _
    rw [PskStoreKey.mf.wf_eq, PskStoreValue.mf.wf_eq]
    exact ⟨wf_knowableBy_of_publishable PreSharedKeyIdShort.mf (label prin m) tr key.pskId h, trivial⟩

section Proofs

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map PskStoreKey PskStoreValue))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map PskStoreKey PskStoreValue))]

/-- Invariant of `initialize_psk_store` (DY*'s `initialize_map_invariant`). -/
@[instance]
public
theorem initializePskStore.proof (prin: Participant):
  HoareTriple
    (initializePskStore prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializePskStore
  exact DySlop.Map.initializeMap.proof prin

variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT OnePskState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT OnePskState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT OnePskState)]

/-- Port of `retrieve_psks_proof`. -/
@[instance]
public
theorem retrievePsks.proof (me: Participant) (sid: Nat) (pskIds: List (PreSharedKeyId Bytes)):
  HoareTriple
    (retrievePsks me sid pskIds)
    (fun tr => PskIdsGood tr pskIds)
    (fun psks tr => PsksBytesInvariant tr psks)
:= by
  induction pskIds with
  | nil =>
    unfold retrievePsks
    step
    grind [PsksBytesInvariant]
  | cons h t ih =>
    unfold retrievePsks
    step
    step
    split
    step
    step by grind [PskIdsGood]
    step
    grind [PsksBytesInvariant, PskIdsGood, Bytes.KnowableBy]

/-- Port of `remember_psk_proof`. -/
@[instance]
public
theorem rememberPsk.proof (me: Participant) (sid: Nat) (pskId: PreSharedKeyIdShort) (psk: Bytes):
  HoareTriple
    (rememberPsk me sid pskId psk)
    (fun tr =>
      PreSharedKeyIdShort.mf.wf (Bytes.Publishable · tr) pskId ∧
      psk.KnowableBy (pskLabel me pskId) tr
    )
    (fun _ _ => True)
:= by
  unfold rememberPsk
  step
  step by
    simp only [MapPred.pred]
    grind
  trivial

end Proofs

end MLS.TreeKEM
