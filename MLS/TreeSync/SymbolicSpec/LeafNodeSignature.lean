module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeSync.Code.Operations
public import DY.Actions.ProtocolEvent

/-!
Port of `MLS.TreeSync.Symbolic.LeafNodeSignature`: the events attesting leaf node signatures,
and the computation of the path to sign (without the signature).

Port-specific differences:
- DyLean's events do not record the principal who triggered them (unlike DY*'s `trigger_event prin`):
  the principal is the field `prin` of the events.
- Events have no tag nor format (MLS*'s `event` instances): DyLean has one trace entry type per event type
  (`ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt)`, `ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt)`).
- The signature predicate (`leaf_node_sign_pred`, …) and the proofs (`parent_hash_implies_event`,
  `state_implies_event`, `is_msg_external_path_to_path`, …) are in `MLS.TreeSync.SymbolicProofs.LeafNodeSignature`.
- `leaf_node_label` is not ported: the label `"LeafNodeTBS"` is written literally
  (as in the tags of the split signature predicate, which `#combine` evaluates).
-/

namespace MLS.TreeSync

open Comparse
open DY
open MLS

/-! ## Events -/

section Events

variable [HasSymbolicBytes]

/-- Port of `leaf_node_signed_event`. -/
public
structure LeafNodeSignedEvent (tkt: TreeKEMTypes Bytes) where
  prin: Participant
  lnTbs: LeafNodeTBS Bytes tkt

/--
Port of `group_has_tree_event`.
The position of the tree (MLS*'s `i`) is part of the tree.
-/
public
structure GroupHasTreeEvent (tkt: TreeKEMTypes Bytes) where
  prin: Participant
  groupId: MlsBytes Bytes
  authentifierLeafIndex: Nat
  l: Nat
  t: TreeSync Bytes tkt l

variable {tkt: TreeKEMTypes Bytes}

/-- Port of `mk_group_has_tree_event`. -/
public
def mkGroupHasTreeEvent (prin: Participant) (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (t: OneTreeSync Bytes tkt):
  GroupHasTreeEvent tkt
:=
  { prin, groupId, authentifierLeafIndex, l := t.1, t := t.2 }

variable [ExecTraceTypes]

/-- Port of `leaf_node_has_event`. -/
public
def LeafNodeHasEvent [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))]
  (prin: Participant) (tr: ExecTrace) (lnTbs: LeafNodeTBS Bytes tkt): Prop
:=
  tr.EventLogged ({ prin, lnTbs }: LeafNodeSignedEvent tkt)

variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt))]

/-- Port of `tree_has_event`. -/
public
def TreeHasEvent (prin: Participant) (tr: ExecTrace)
  (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (t: OneTreeSync Bytes tkt): Prop
:=
  tr.EventLogged (mkGroupHasTreeEvent prin groupId authentifierLeafIndex t)

/-- Port of `tree_list_has_event`. -/
public
def TreeListHasEvent (prin: Participant) (tr: ExecTrace)
  (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (tl: TreeSyncList Bytes tkt): Prop
:=
  ∀ t ∈ tl, TreeHasEvent prin tr groupId authentifierLeafIndex t

end Events

/-! ## Path signature -/

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `external_path_to_path_aux_nosig`.
MLS* requires `(get_path_leaf p).source == LNS_update`; otherwise, the leaf source is overwritten with `commit` anyway.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def externalPathToPathAuxNosig {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l):
  Result (LeafNode Bytes tkt)
:= do
  let computedParentHash ← computeLeafParentHashFromPath t li p rootParentHash.val
  let computedParentHash ← mkMlsBytes computedParentHash "external_path_to_path_aux_nosig" "computed_parent_hash"
  let lp := p.getPathLeaf
  let newLpData: LeafNodeData Bytes tkt := {
    lp with
    source := .commit
    lifetime := ()
    parentHash := computedParentHash
  }
  pure { data := newLpData, signature := MlsBytes.empty }

/--
Port of `external_path_to_path_nosig`.
MLS* requires `(get_path_leaf p).source == LNS_update`; otherwise, the leaf source is overwritten with `commit` anyway.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def externalPathToPathNosig {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l):
  Result (PathSync Bytes tkt l)
:= do
  let newLeafNode ← externalPathToPathAuxNosig t li p
  pure (p.setPathLeaf newLeafNode)

end CryptoBytes

section ExternalPathHasEvent

variable [HasSymbolicBytes] {tkt: TreeKEMTypes Bytes} [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt))]

/--
Port of `external_path_has_event`.
MLS*'s `path_to_tree_list_pre (tree_has_event …) t auth_p` is stated with the result of `pathToTreeList`
(MLS*'s `path_to_tree_list_pre_lemma`), whose success follows from the success of `externalPathToPathNosig` in MLS*.
-/
public
def ExternalPathHasEvent {l: Nat} (prin: Participant) (tr: ExecTrace)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes): Prop
:=
  p.getPathLeaf.source = .update ∧
  li < 2^32 ∧
  ∃ authP, externalPathToPathNosig t li p = .success authP ∧ (
    let authLn := authP.getPathLeaf
    LeafNodeHasEvent prin tr
      { data := authLn.data, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 } ∧
    ∃ tl, pathToTreeList t li authP = .success tl ∧ TreeListHasEvent prin tr groupId li tl
  )

end ExternalPathHasEvent

end MLS.TreeSync
