module

public import MLS.TreeSync.SymbolicSpec.State.GroupManager
public import DySlop.Lib.State.Map
import all MLS.TreeSync.SymbolicSpec.State.GroupManager

/-!
Port of the invariant of `MLS.TreeSync.Symbolic.State.GroupManager`:
the group identifiers are publishable.

Port-specific differences:
- The map predicate has no session identifier (see `DySlop.Map.MapPred`). It is an instance of `MapPred`,
  which gives the invariant of the maps: MLS*'s `has_group_manager_invariant` is not needed.
- The proofs of the API functions (DY*'s `initialize_map_invariant`, … in MLS*) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the map.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.PersistentLocalState
open MLS
open DySlop.Map (Map MapPred)

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (Map GroupManagerKey GroupManagerValue))]

/-- Port of `group_manager_pred`. -/
public
instance groupManagerPred: MapPred GroupManagerKey GroupManagerValue where
  pred tr _ key _ := key.groupId.val.Publishable tr
  pred_later tr1 tr2 prin key value := by
    grind
  pred_knowable tr prin key value m _ h := by
    show GroupManagerKey.mf.wf _ _ ∧ GroupManagerValue.mf.wf _ _
    simp only [GroupManagerKey.mf.wf_eq, GroupManagerValue.mf.wf_eq]
    grind [Bytes.Publishable, Bytes.KnowableBy, canFlowTrans]

section Proofs

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map GroupManagerKey GroupManagerValue))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map GroupManagerKey GroupManagerValue))]

/-- Invariant of `initialize_group_manager` (DY*'s `initialize_map_invariant`). -/
@[instance]
public
theorem initializeGroupManager.proof (prin: Participant):
  HoareTriple
    (initializeGroupManager prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeGroupManager
  exact DySlop.Map.initializeMap.proof prin

/-- Invariant of `add_new_group_sessions` (DY*'s `add_key_value_invariant`). -/
@[instance]
public
theorem addNewGroupSessions.proof (prin: Participant) (sid: Nat) (key: GroupManagerKey) (value: GroupManagerValue):
  HoareTriple
    (addNewGroupSessions prin sid key value)
    (fun tr => MapPred.pred tr prin key value)
    (fun _ _ => True)
:= by
  unfold addNewGroupSessions
  exact DySlop.Map.addKeyValue.proof prin sid key value

/-- Invariant of `find_group_sessions` (DY*'s `find_value_invariant`). -/
@[instance]
public
theorem findGroupSessions.proof (prin: Participant) (sid: Nat) (key: GroupManagerKey):
  HoareTriple
    (findGroupSessions prin sid key)
    (fun _ => True)
    (fun value tr => MapPred.pred tr prin key value)
:= by
  unfold findGroupSessions
  exact DySlop.Map.findValue.proof prin sid key

end Proofs

end MLS.TreeSync
