module

public import MLS.TreeSync.SymbolicSpec.State.KeyPackageManager
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeSync.SymbolicSpec.State.KeyPackageManager

/-!
Port of the invariant of `MLS.TreeSync.Symbolic.State.KeyPackageManager`:
the key packages are publishable.

Port-specific differences:
- The map predicate has no session identifier (see `DySlop.Map.MapPred`). It is an instance of `MapPred`,
  which gives the invariant of the maps: MLS*'s `has_key_package_manager_invariant` is not needed.
- The proofs of the API functions (DY*'s `initialize_map_invariant`, … in MLS*) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the map.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.Bootstrap
open DySlop.Map (Map MapPred)

variable [HasSymbolicInvariants] (tkt: TreeKEMTypes Bytes)
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]

/-- Port of `key_package_manager_pred`. -/
public
instance keyPackageManagerPred: MapPred (KeyPackage Bytes tkt) KeyPackageManagerValue where
  pred tr _ keyPackage _ := (KeyPackage.mf tkt).wf (Bytes.Publishable · tr) keyPackage
  pred_later tr1 tr2 prin key value := by
    grind
  pred_knowable tr prin key value m _ h := by
    show (KeyPackage.mf tkt).wf _ _ ∧ KeyPackageManagerValue.mf.wf _ _
    rw [KeyPackageManagerValue.mf.wf_eq]
    exact ⟨wf_knowableBy_of_publishable (KeyPackage.mf tkt) (label prin m) tr key h, trivial⟩

section Proofs

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]

/-- Invariant of `initialize_key_package_manager` (DY*'s `initialize_map_invariant`). -/
@[instance]
public
theorem initializeKeyPackageManager.proof (prin: Participant):
  HoareTriple
    (initializeKeyPackageManager tkt prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeKeyPackageManager
  exact DySlop.Map.initializeMap.proof prin

/-- Invariant of `add_new_key_package_secret_session` (DY*'s `add_key_value_invariant`). -/
@[instance]
public
theorem addNewKeyPackageSecretSession.proof (prin: Participant) (sid: Nat)
  (key: KeyPackage Bytes tkt) (value: KeyPackageManagerValue):
  HoareTriple
    (addNewKeyPackageSecretSession tkt prin sid key value)
    (fun tr => MapPred.pred tr prin key value)
    (fun _ _ => True)
:= by
  unfold addNewKeyPackageSecretSession
  exact DySlop.Map.addKeyValue.proof prin sid key value

/-- Invariant of `find_key_package_secret_session` (DY*'s `find_value_invariant`). -/
@[instance]
public
theorem findKeyPackageSecretSession.proof (prin: Participant) (sid: Nat) (key: KeyPackage Bytes tkt):
  HoareTriple
    (findKeyPackageSecretSession tkt prin sid key)
    (fun _ => True)
    (fun value tr => MapPred.pred tr prin key value)
:= by
  unfold findKeyPackageSecretSession
  exact DySlop.Map.findValue.proof prin sid key

end Proofs

end MLS.TreeSync
