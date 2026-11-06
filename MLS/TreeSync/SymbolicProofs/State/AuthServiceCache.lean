module

public import MLS.TreeSync.SymbolicSpec.State.AuthServiceCache
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
public import MLS.Symbolic.SymbolicProofs.Symbolic
public import MLS.TreeSync.SymbolicProofs.AuthService.CredentialInterpretation
import all MLS.TreeSync.SymbolicSpec.State.AuthServiceCache
import DY.Meta.Step

/-!
Port of the invariant of `MLS.TreeSync.Symbolic.State.AuthServiceCache`:
the cached tokens are accepted by the Authentication Service.

Port-specific differences:
- The map predicate has no session identifier (see `DySlop.Map.MapPred`). It is an instance of `MapPred`,
  which gives the invariant of the maps: MLS*'s `has_as_cache_invariant` is not needed.
- The proofs of the API functions (DY*'s `initialize_map_invariant`, … in MLS*) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the map.
- `verifyCredential.proof` is not in MLS* (see `MLS.TreeSync.verifyCredential`).
-/

namespace MLS.TreeSync

open Comparse
open DY DY.PersistentLocalState
open MLS
open DySlop.Map (Map MapPred)

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (Map AsCacheKey AsCacheValue))]

/-- Port of `as_cache_pred`. -/
public
instance asCachePred: MapPred AsCacheKey AsCacheValue where
  pred tr _ key value :=
    (dyAsp tr).credentialOk (key.verificationKey, key.credential) value.token ∧
    key.verificationKey.val.Publishable tr ∧
    Credential.mf.wf (Bytes.Publishable · tr) key.credential
  pred_later tr1 tr2 prin key value := by
    grind
  pred_knowable tr prin key value m _ h := by
    have := wf_knowableBy_of_publishable Credential.mf (label prin m) tr key.credential
    show AsCacheKey.mf.wf _ _ ∧ AsCacheValue.mf.wf _ _
    simp only [AsCacheKey.mf.wf_eq, AsCacheValue.mf.wf_eq]
    grind [Bytes.Publishable, Bytes.KnowableBy, canFlowTrans]

section Proofs

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]

/-- Invariant of `initialize_as_cache` (DY*'s `initialize_map_invariant`). -/
@[instance]
public
theorem initializeAsCache.proof (prin: Participant):
  HoareTriple
    (initializeAsCache prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeAsCache
  exact DySlop.Map.initializeMap.proof prin

/-- Invariant of `add_verified_credential` (DY*'s `add_key_value_invariant`). -/
@[instance]
public
theorem addVerifiedCredential.proof (prin: Participant) (sid: Nat) (key: AsCacheKey) (value: AsCacheValue):
  HoareTriple
    (addVerifiedCredential prin sid key value)
    (fun tr => MapPred.pred tr prin key value)
    (fun _ _ => True)
:= by
  unfold addVerifiedCredential
  exact DySlop.Map.addKeyValue.proof prin sid key value

/-- Invariant of `find_verified_credential` (DY*'s `find_value_invariant`). -/
@[instance]
public
theorem findVerifiedCredential.proof (prin: Participant) (sid: Nat) (key: AsCacheKey):
  HoareTriple
    (findVerifiedCredential prin sid key)
    (fun _ => True)
    (fun value tr => MapPred.pred tr prin key value)
:= by
  unfold findVerifiedCredential
  exact DySlop.Map.findValue.proof prin sid key

attribute [local instance] getTimestamp.proof_eq in
/-- Invariant of `verifyCredential`: the token is the current time, at which `who` has its signature key. -/
@[instance]
public
theorem verifyCredential.proof
  [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
  [TraceInvariant.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
  (me: Participant) (authServiceSid: Nat) (who: Participant) (whoSignatureKeySid: Nat):
  HoareTriple
    (verifyCredential me authServiceSid who whoSignatureKeySid)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold verifyCredential
  step
  step
  split
  · step
    -- `time = tr.length` cannot be monotonized: substitute it
    rename_i hcred htime
    subst htime
    step by
      simp only [MapPred.pred, dyAsp, credentialToPrincipal_principalToCredential _ _ hcred,
        Trace.prefix_length_eq_self, Nat.le_refl, true_and]
      obtain rfl := (mkMlsBytes_eq_success _ _ _ _).1 ‹_›
      have := principalToCredential_wf tr _ _ hcred
      grind [IsSignatureKeyVk]
    trivial
  · step

end Proofs

end MLS.TreeSync
