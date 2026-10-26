module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeKEM.Code.API.KeySchedule.Types
public import MLS.TreeSync.Code.Types
public import MLS.Bootstrap.Code.NetworkTypes
public import DY.Actions.ProtocolEvent

/-!
Port of `MLS.TreeKEM.Symbolic.EpochEvent`: the event logged when a principal enters a new epoch of a group.

Port-specific differences:
- DyLean's events do not record the principal who triggered them (unlike DY*'s `trigger_event prin`):
  the principal is the field `prin` of the event.
- The event has no tag nor format (MLS*'s `event` instance):
  the formats used only by it (`ps_psks`, `all_keyschedule_keys`, `ps_treekem_keyschedule_state`) are not ported.
- Trees are compared as dependent pairs (see `MLS.TreeSync.OneTreeSync`).
- Only the specification is ported for now: the event predicate (`i_am_in_group_pred`, …) is not ported yet.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open MLS MLS.TreeSync MLS.Bootstrap

variable [HasSymbolicBytes]

/-- Port of `i_just_joined_group`. -/
public
structure IJustJoinedGroup where
  inviter: Nat

/-- Port of `commit_type`. -/
public
inductive CommitType where
  | addOnlyCommit
  | fullCommit
deriving DecidableEq

/-- Port of `i_processed_commit_group`. -/
public
structure IProcessedCommitGroup where
  previousInitSecret: Bytes
  previousGroupContext: GroupContext Bytes
  previousTreeHeight: Nat
  previousTree: TreeSync Bytes tkt previousTreeHeight
  commitTy: CommitType
  joiners: List (KeyPackage Bytes tkt)

/-- Port of `how_am_i_in_group`. -/
public
inductive HowAmIInGroup where
  | justCreated
  | justJoined (x: IJustJoinedGroup)
  | processedCommit (x: IProcessedCommitGroup)

/-- Port of `i_am_in_group`. -/
public
structure IAmInGroup where
  prin: Participant
  how: HowAmIInGroup
  groupContext: GroupContext Bytes
  treeHeight: Nat
  tree: TreeSync Bytes tkt treeHeight
  psks: List (PreSharedKeyId Bytes × Bytes)
  epochKeys: TreeKEMKeyscheduleState Bytes

/-- Port of `joiner_is_stale_participant`. -/
public
def JoinerIsStaleParticipant {l: Nat} (tree: TreeSync Bytes tkt l) (joiner: KeyPackage Bytes tkt): Prop :=
  ∃ li,
    leafAt tree li = some joiner.tbs.leafNode ∧
    joiner.tbs.leafNode.data.source = .keyPackage

/-- Port of `joiners_are_stale_participants`. -/
public
def JoinersAreStaleParticipants {l: Nat} (tree: TreeSync Bytes tkt l) (joiners: List (KeyPackage Bytes tkt)): Prop :=
  ∀ joiner ∈ joiners, JoinerIsStaleParticipant tree joiner

/-- Port of `has_same_event_as_me`. -/
public
def HasSameEventAsMe (inviterEv: IAmInGroup)
  (groupContext: GroupContext Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (epochKeys: TreeKEMKeyscheduleState Bytes):
  Prop
:=
  inviterEv.groupContext = groupContext ∧
  inviterEv.epochKeys = epochKeys ∧
  inviterEv.psks = psks ∧
  match inviterEv.how with
  | .processedCommit x => JoinersAreStaleParticipants inviterEv.tree x.joiners
  | _ => False

variable [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)]

/-- Port of `inviter_has_same_event_as_me`. -/
public
def InviterHasSameEventAsMe (tr: ExecTrace) (inviterId: Participant)
  (groupContext: GroupContext Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (epochKeys: TreeKEMKeyscheduleState Bytes):
  Prop
:=
  ∃ inviterEv,
    HasSameEventAsMe inviterEv groupContext psks epochKeys ∧
    inviterEv.prin = inviterId ∧
    tr.EventLogged inviterEv

/-- Port of `i_have_previous_epoch_event_with_witness`. -/
public
def IHavePreviousEpochEventWithWitness {previousTreeHeight: Nat} (tr: ExecTrace) (me: Participant)
  (previousGroupContext: GroupContext Bytes) (previousInitSecret: Bytes) (previousTree: TreeSync Bytes tkt previousTreeHeight)
  (previousEv: IAmInGroup): Prop
:=
  previousEv.prin = me ∧
  tr.EventLogged previousEv ∧
  previousEv.groupContext = previousGroupContext ∧
  (⟨previousEv.treeHeight, previousEv.tree⟩: OneTreeSync Bytes tkt) = ⟨previousTreeHeight, previousTree⟩ ∧
  previousEv.epochKeys.initSecret = previousInitSecret

/-- Port of `i_have_previous_epoch_event`. -/
public
def IHavePreviousEpochEvent {previousTreeHeight: Nat} (tr: ExecTrace) (me: Participant)
  (previousGroupContext: GroupContext Bytes) (previousInitSecret: Bytes) (previousTree: TreeSync Bytes tkt previousTreeHeight):
  Prop
:=
  ∃ previousEv, IHavePreviousEpochEventWithWitness tr me previousGroupContext previousInitSecret previousTree previousEv

end MLS.TreeKEM
