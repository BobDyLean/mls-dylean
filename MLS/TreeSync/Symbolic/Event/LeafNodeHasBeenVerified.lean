module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeSync.Code.Types
public import DY.Actions.ProtocolEvent

/-!
Port of `MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified`:
an event logged when a principal verifies a leaf node.

Port-specific differences:
- DyLean's events do not record the principal who triggered them (unlike DY*'s `trigger_event prin`):
  the principal is the field `prin` of the event.
- The event has no tag nor format (MLS*'s `event` instance):
  DyLean has one trace entry type per event type (`ProtocolEvent.ExecEntryT (LeafNodeHasBeenVerified tkt)`).
- Only the specification is ported for now: the event predicate (`leaf_node_has_been_verified_pred`, …)
  and the lemmas are not ported yet.
-/

namespace MLS.TreeSync

open Comparse
open DY
open MLS

variable [HasSymbolicBytes]

/-- Port of `leaf_node_has_been_verified`. -/
public
structure LeafNodeHasBeenVerified (tkt: TreeKEMTypes Bytes) where
  prin: Participant
  leafNode: LeafNode Bytes tkt
  groupId: MlsBytes Bytes
  leafIndex: Nat

variable {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeHasBeenVerified tkt))]

/-- Port of `i_have_verified_leaf_node`. -/
public
def IHaveVerifiedLeafNode (tr: ExecTrace) (me: Participant)
  (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Prop
:=
  tr.EventLogged ({ prin := me, leafNode, groupId, leafIndex }: LeafNodeHasBeenVerified tkt)

/-- Port of `i_have_verified_every_leaf_node`. -/
public
def IHaveVerifiedEveryLeafNode {l: Nat} (tr: ExecTrace) (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Prop
:=
  match t.intoLeftRightView with
  | .leaf none _ => True
  | .leaf (some ln) i => IHaveVerifiedLeafNode tr me ln groupId i
  | .node _ left right =>
    IHaveVerifiedEveryLeafNode tr me left groupId ∧
    IHaveVerifiedEveryLeafNode tr me right groupId
termination_by l

/-- Port of `log_leaf_node_verification_event`. -/
public
def logLeafNodeVerificationEvent (me: Participant)
  (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Traceful Unit
:=
  ProtocolEvent.logEvent ({ prin := me, leafNode, groupId, leafIndex }: LeafNodeHasBeenVerified tkt)

/-- Port of `log_leaf_node_verification_events`. -/
public
def logLeafNodeVerificationEvents {l: Nat} (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Traceful Unit
:=
  match t.intoLeftRightView with
  | .leaf none _ => pure ()
  | .leaf (some ln) i => logLeafNodeVerificationEvent me ln groupId i
  | .node _ left right => do
    logLeafNodeVerificationEvents me left groupId
    logLeafNodeVerificationEvents me right groupId
termination_by l

end MLS.TreeSync
