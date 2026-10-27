module

public import MLS.TreeKEM.SymbolicProofs.State.NodeKey
public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeKEM.Code.Operations
public import MLS.Bootstrap.SymbolicProofs.KeyPackage
public import MLS.TreeSync.SymbolicProofs.LeafNodeSignature
public import MLS.TreeSync.SymbolicProofs.Event.LeafNodeHasBeenVerified
public import DySlop.Lib.Label
public import DySlop.Lib.Event
import all MLS.TreeSync.SymbolicSpec.LeafNodeSignature
import all MLS.TreeSync.SymbolicSpec.Event.LeafNodeHasBeenVerified

/-!
Port of `MLS.TreeKEM.Symbolic.Tree.Labels`:
the labels of the TreeKEM node keys of a TreeSync tree,
and the proof that the node keys of a tree verified by a principal have the expected labels and usages
(`proveAllTreeKeysGood`), using the guarantees of TreeSync (`MLS.TreeSync.SymbolicProofs.LeafNodeSignature`).

Port-specific differences:
- `one_path_secret_usage` contains the tree, whose position is MLS*'s `i`.
  The list of path secret usages is serialized with `slowList` (MLS* uses Comparse's `ps_whole_list`).
- The trace entries are the bundles `HasTreeSyncExecTrace tkt` and `HasTreeKEMExecTrace`.
- `get_node_content` returns the empty bytestring on blank nodes (MLS* requires `node_not_blank t`).
- `is_root_node_pk` drops the length of the public key, only needed for MLS*'s refinement `hpke_public_key`.
- The event predicates are registered with `ProtocolEvent.EventInv.Has` (DY*'s `has_event_pred`),
  and MLS*'s `has_treesync_treekem_link_invariants` is the class `HasTreesyncTreekemLinkInvariants`,
  bundling the instances of the trace invariant needed by the proofs.
- `all_tree_keys_good` states the property of non-blank nodes with `nodeNotBlank` (MLS* matches on the node content).
- The labels of trees are characterized by the leaves of the tree (`nodeSkLabelAux_isCorrupt`):
  MLS*'s lemmas comparing them (e.g. `node_sk_label_flows_to_node_sk_label_nosig`) follow from this characterization.
- MLS*'s `get_authentifier_index` is the predicate `IsAuthentifierIndex` (see `MLS.TreeSync.SymbolicProofs.LeafNodeSignature`):
  the lemmas about the authentifier take its index as an argument.
- The trace invariant gives the event predicates on prefixes of the proof trace,
  and corruption is on the erased trace (`tr.erase`), as in `MLS.TreeSync.SymbolicProofs.LeafNodeSignature`.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open DySlop.HPKE
open MLS MLS.TreeSync MLS.Bootstrap

/-! ## Path secret stuff -/

section PathSecretUsage

variable [HasSymbolicBytes]

/-- Port of `one_path_secret_usage`. The position of the tree (MLS*'s `i`) is part of the tree. -/
public
structure OnePathSecretUsage where
  l: Nat
  t: TreeSync Bytes tkt l
  groupId: MlsBytes Bytes
  committerLeafIndex: Nat

namespace OnePathSecretUsage

public
abbrev Raw := ((l: Nat) × TreeSync Bytes tkt l) × MlsBytes Bytes × Nat

@[expose]
public
def f: Raw → OnePathSecretUsage :=
  fun (⟨l, t⟩, groupId, committerLeafIndex) => { l, t, groupId, committerLeafIndex }

@[expose]
public
def g: OnePathSecretUsage → Raw :=
  fun { l, t, groupId, committerLeafIndex } => (⟨l, t⟩, groupId, committerLeafIndex)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end OnePathSecretUsage

/-- Port of `ps_one_path_secret_usage`. -/
@[expose]
public
def OnePathSecretUsage.mf: NonExtensibleMessageFormat Bytes OnePathSecretUsage :=
  .isomorphic (.prod (.sigma .slowNat (TreeSync.mf tkt)) (.prod MlsBytes.mf .slowNat)) OnePathSecretUsage.f OnePathSecretUsage.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem OnePathSecretUsage.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: OnePathSecretUsage):
  OnePathSecretUsage.mf.wf pred x = ((TreeSync.mf tkt x.l).wf pred x.t ∧ pred x.groupId.val)
:= by
  simp [OnePathSecretUsage.mf, OnePathSecretUsage.g]

/-- Port of `path_secret_usage`. -/
public
abbrev PathSecretUsage := List OnePathSecretUsage

/-- Port of `parseable_serializeable_path_secret_usage`. -/
@[expose]
public
def PathSecretUsage.mf: NonExtensibleMessageFormat Bytes PathSecretUsage :=
  .slowList OnePathSecretUsage.mf

public
instance: PathSecretUsage.mf.IsNonAmbiguous := by
  unfold PathSecretUsage.mf
  infer_instance

/-- Parse the path secret usages in the data of a usage (MLS*'s `parse path_secret_usage (KdfExpandKey?.data prk_usage)`). -/
@[expose]
public
def PathSecretUsage.ofUsage (usg: Usage): Option PathSecretUsage :=
  usg.data.bind PathSecretUsage.mf.toExtensible.parse

/-- The usage of path secrets whose remaining usages are `x`. -/
@[expose]
public
def PathSecretUsage.toUsage (x: PathSecretUsage): Usage :=
  Usage.kdfExpandKey "MLS.PathSecret" (serializeNE PathSecretUsage.mf x)

@[simp]
public
theorem PathSecretUsage.ofUsage_toUsage (x: PathSecretUsage):
  PathSecretUsage.ofUsage x.toUsage = some x
:= by
  simp [PathSecretUsage.ofUsage, PathSecretUsage.toUsage, Usage.kdfExpandKey, serializeNE,
    ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv]

end PathSecretUsage

section RootNodePk

variable [HasSymbolicInvariants]

/--
Port of `is_root_node_pk`.
MLS* also requires `length node_pk == hpke_public_key_length`, only needed for its refinement `hpke_public_key`.
-/
@[expose]
public
def IsRootNodePk (tr: ProofTrace) (nodePk: Bytes): Prop :=
  ∃ pathSecret nodeSk,
    deriveKeypairFromPathSecret pathSecret = .success (nodeSk, nodePk) ∧
    pathSecret.Invariant tr ∧
    pathSecret.HasUsage (PathSecretUsage.toUsage []) tr

/-- Root node public keys stay root node public keys when the trace grows. -/
public
theorem IsRootNodePk_later (tr1 tr2: ProofTrace) (nodePk: Bytes)
  : tr1 ≤ tr2 →
    IsRootNodePk tr1 nodePk →
    IsRootNodePk tr2 nodePk
:= by
  grind [IsRootNodePk]

grind_pattern IsRootNodePk_later => tr1 ≤ tr2, IsRootNodePk tr1 nodePk
grind_pattern [grind_later] IsRootNodePk_later => tr1 ≤ tr2, IsRootNodePk tr1 nodePk

end RootNodePk

/-! ## Leaf node verification event label -/

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-- Port of `principal_leaf_node_has_been_verified_label`. -/
@[expose]
public
def principalLeafNodeHasBeenVerifiedLabel (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat)
  (prin: Participant): Label
:=
  ProtocolEvent.label ({ prin, leafNode, groupId, leafIndex }: LeafNodeHasBeenVerified tkt)

/-- Port of `leaf_node_has_been_verified_label`. -/
@[expose]
public
def leafNodeHasBeenVerifiedLabel (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Label :=
  Label.bigJoin (principalLeafNodeHasBeenVerifiedLabel leafNode groupId leafIndex)

/-- Port of `guarded_signature_key_label`. -/
@[expose]
public
def guardedSignatureKeyLabel (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Label :=
  match credentialToPrincipal leafNode.data.credential with
  | none => Label.unknown
  | some prin =>
    Label.guarded
      (signatureKeyLabel prin leafNode.data.signatureKey.val)
      (leafNodeHasBeenVerifiedLabel leafNode groupId leafIndex)

end Labels

/--
Port of `get_node_content`.
MLS* requires `node_not_blank t`; otherwise, the empty bytestring is returned.
-/
@[expose]
public
def getNodeContent [HasSymbolicBytes] {l: Nat} (t: TreeSync Bytes tkt l): Bytes :=
  match t.intoLeftRightView with
  | .leaf (some ln) _ => ln.data.content.val
  | .node (some pn) _ _ => pn.content.val
  | _ => BytesLike.empty

/-- Port of `node_label_type`. -/
public
inductive NodeLabelType where
  | noCommitter (li: Nat)
  | noCommitterSignature (li: Nat)
  | yesCommitter
deriving DecidableEq

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-- Port of `node_sk_label_aux_leaf`. -/
@[expose]
public
def nodeSkLabelAuxLeaf (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (ty: NodeLabelType) (i: Nat): Label :=
  if ty = .noCommitter i then Label.secret
  else
    let sigLabel :=
      if ty = .noCommitterSignature i then Label.secret
      else guardedSignatureKeyLabel ln groupId i
    match credentialToPrincipal ln.data.credential with
    | none => Label.unknown
    | some prin =>
      match ln.data.source with
      | .keyPackage =>
        sigLabel.join ((nodeKeyLabel prin ln.data.content.val).join (initKeyAssociatedWith ln))
      | .update | .commit =>
        sigLabel.join (nodeKeyLabel prin ln.data.content.val)

/-- Port of `node_sk_label_aux`. -/
@[expose]
public
def nodeSkLabelAux {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (ty: NodeLabelType): Label :=
  match t.intoLeftRightView with
  | .leaf none _ => Label.secret
  | .leaf (some ln) i => nodeSkLabelAuxLeaf ln groupId ty i
  | .node _ left right => (nodeSkLabelAux left groupId ty).join (nodeSkLabelAux right groupId ty)
termination_by l

/-- Port of `node_sk_label_nocommitter`. -/
@[expose]
public
def nodeSkLabelNocommitter {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat): Label :=
  nodeSkLabelAux t groupId (.noCommitter li)

/-- Port of `node_sk_label_nosig`. -/
@[expose]
public
def nodeSkLabelNosig {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat): Label :=
  nodeSkLabelAux t groupId (.noCommitterSignature li)

/-- Port of `node_sk_label`. -/
@[expose]
public
def nodeSkLabel {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Label :=
  nodeSkLabelAux t groupId .yesCommitter

/-- Port of `node_sk_label_canon_nosig`. -/
@[expose]
public
def nodeSkLabelCanonNosig {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat): Label :=
  nodeSkLabelAux (canonicalizeUnmergedLeaves t) groupId (.noCommitterSignature li)

/-- Port of `node_sk_label_canon`. -/
@[expose]
public
def nodeSkLabelCanon {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Label :=
  nodeSkLabelAux (canonicalizeUnmergedLeaves t) groupId .yesCommitter

/-! ## Corruption lemmas -/

omit [HasTreeSyncExecTrace tkt] in
/-- The label of the verification of a leaf node is corrupt when some principal has verified it. -/
theorem leafNodeHasBeenVerifiedLabel_isCorrupt (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat)
  (tr: ExecTrace):
  (leafNodeHasBeenVerifiedLabel leafNode groupId leafIndex).isCorrupt tr ↔
    ∃ prin, tr.EventLogged ({ prin, leafNode, groupId, leafIndex }: LeafNodeHasBeenVerified tkt)
:= by
  simp [leafNodeHasBeenVerifiedLabel, principalLeafNodeHasBeenVerifiedLabel, ProtocolEvent.label_isCorrupt]

/--
Port of `guarded_signature_key_label_is_corrupt`.
MLS*'s `prefix tr (find_event_triggered_at_timestamp tr me …)` is the prefix before the first time the event was logged.
-/
public
theorem guardedSignatureKeyLabel_isCorrupt (tr: ExecTrace) (me prin: Participant)
  (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat)
  (h: (guardedSignatureKeyLabel leafNode groupId leafIndex).isCorrupt tr)
  (hprin: credentialToPrincipal leafNode.data.credential = some prin)
  (hev: IHaveVerifiedLeafNode tr me leafNode groupId leafIndex):
  ∃ i, tr.EventFirstLoggedAt ({ prin := me, leafNode, groupId, leafIndex }: LeafNodeHasBeenVerified tkt) i ∧
    (signatureKeyLabel prin leafNode.data.signatureKey.val).isCorrupt (tr.prefix i)
:= by
  simp only [guardedSignatureKeyLabel, hprin] at h
  apply Label.isCorrupt_guarded_event _ _ _ _ hev
  apply Label.guarded_canFlow _ _ _ _ _ _ (fun _ => canFlowRefl _ _) _ (Trace.le_refl tr) h
  exact fun _ => Label.bigJoin_canFlow _ me _

end Labels

/-! ## Event invariants (link with TreeSync) -/

section EventPredicates

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-- Port of `group_has_tree_event_pred`. -/
@[expose]
public
def groupHasTreeEventPred (tr: ProofTrace) (ev: GroupHasTreeEvent tkt): Prop :=
  nodeNotBlank ev.t ∧
  (getNodeContent ev.t).Invariant tr ∧
  (nodeSkLabelCanonNosig ev.t ev.groupId ev.authentifierLeafIndex).canFlow ((getNodeContent ev.t).hpkeSkLabel tr) tr.erase ∧
  (getNodeContent ev.t).HpkeSkHasUsage nodeKeyUsage tr ∧
  ((1 ≤ ev.l ∧ getParentHashOf ev.t = some rootParentHash) → IsRootNodePk tr (getNodeContent ev.t))

/-- Port of `leaf_node_signed_event_pred`. -/
@[expose]
public
def leafNodeSignedEventPred (tr: ProofTrace) (ev: LeafNodeSignedEvent tkt): Prop :=
  match ev.lnTbs.data.source with
  | .keyPackage =>
    ev.lnTbs.data.content.val.Invariant tr ∧
    (nodeKeyLabel ev.prin ev.lnTbs.data.content.val).canFlow (ev.lnTbs.data.content.val.hpkeSkLabel tr) tr.erase ∧
    ev.lnTbs.data.content.val.HpkeSkHasUsage nodeKeyUsage tr
  | _ => True

/--
Port of `has_treesync_treekem_link_invariants`:
the signature predicate of leaf nodes and the event predicates linking TreeSync and TreeKEM are in the protocol invariants.
The fields are scoped instances in the namespace `MLS.TreeKEM`; the top-level protocol provides them
(`instance: HasTreesyncTreekemLinkInvariants where`).
-/
public
class HasTreesyncTreekemLinkInvariants [TraceInvariant] where
  [leafNodeTbs: SignWithLabelPred.Has (leafNodeSignPred tkt)]
  [proofTrace0: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (LeafNodeHasBeenVerified tkt))]
  [eventInv0: ProtocolEvent.EventInv (LeafNodeHasBeenVerified tkt)]
  [traceInv0: TraceInvariant.Has (ProtocolEvent.ProofEntryT (LeafNodeHasBeenVerified tkt))]
  [eventPred0: ProtocolEvent.EventInv.Has (leafNodeHasBeenVerifiedPred (tkt := tkt))]
  [proofTrace1: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]
  [eventInv1: ProtocolEvent.EventInv (GroupHasTreeEvent tkt)]
  [traceInv1: TraceInvariant.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]
  [eventPred1: ProtocolEvent.EventInv.Has groupHasTreeEventPred]
  [proofTrace2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
  [eventInv2: ProtocolEvent.EventInv (LeafNodeSignedEvent tkt)]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
  [eventPred2: ProtocolEvent.EventInv.Has leafNodeSignedEventPred]

attribute [scoped instance] HasTreesyncTreekemLinkInvariants.leafNodeTbs
attribute [reducible, scoped instance] HasTreesyncTreekemLinkInvariants.proofTrace0
attribute [scoped instance] HasTreesyncTreekemLinkInvariants.traceInv0
attribute [reducible, scoped instance] HasTreesyncTreekemLinkInvariants.eventInv0
attribute [scoped instance] HasTreesyncTreekemLinkInvariants.eventPred0
attribute [reducible, scoped instance] HasTreesyncTreekemLinkInvariants.proofTrace1
attribute [scoped instance] HasTreesyncTreekemLinkInvariants.traceInv1
attribute [reducible, scoped instance] HasTreesyncTreekemLinkInvariants.eventInv1
attribute [scoped instance] HasTreesyncTreekemLinkInvariants.eventPred1
attribute [reducible, scoped instance] HasTreesyncTreekemLinkInvariants.proofTrace2
attribute [scoped instance] HasTreesyncTreekemLinkInvariants.traceInv2
attribute [reducible, scoped instance] HasTreesyncTreekemLinkInvariants.eventInv2
attribute [scoped instance] HasTreesyncTreekemLinkInvariants.eventPred2

end EventPredicates

/-! ## Main property established by this module -/

section Good

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-- Port of `node_key_good`. MLS* requires `node_not_blank t`. -/
@[expose]
public
def NodeKeyGood {l: Nat} (tr: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Prop :=
  (getNodeContent t).Invariant tr ∧
  (nodeSkLabelCanon t groupId).canFlow ((getNodeContent t).hpkeSkLabel tr) tr.erase ∧ (
    (
      (getNodeContent t).HpkeSkHasUsage nodeKeyUsage tr ∧
      ((1 ≤ l ∧ getParentHashOf t = some rootParentHash) → IsRootNodePk tr (getNodeContent t))
    ) ∨ (
      (nodeSkLabelCanon t groupId).canFlow Label.pub tr.erase
    )
  )

/--
Port of `all_tree_keys_good`.
MLS* states `node_key_good` on the non-blank leaves and nodes by matching on their content;
here, it is stated with `nodeNotBlank`.
-/
@[expose]
public
def AllTreeKeysGood {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (tr: ProofTrace): Prop :=
  (nodeNotBlank t → NodeKeyGood tr t groupId) ∧
  match t.intoLeftRightView with
  | .leaf _ _ => True
  | .node _ left right => AllTreeKeysGood left groupId tr ∧ AllTreeKeysGood right groupId tr
termination_by l

public
theorem AllTreeKeysGood_zero (t: TreeSync Bytes tkt 0) (groupId: MlsBytes Bytes) (tr: ProofTrace):
  AllTreeKeysGood t groupId tr ↔ (nodeNotBlank t → NodeKeyGood tr t groupId)
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  rw [AllTreeKeysGood.eq_def]
  grind

public
theorem AllTreeKeysGood_left_right {l: Nat} (t: TreeSync Bytes tkt (l+1)) (groupId: MlsBytes Bytes) (tr: ProofTrace):
  AllTreeKeysGood t groupId tr ↔
    (nodeNotBlank t → NodeKeyGood tr t groupId) ∧ AllTreeKeysGood t.left groupId tr ∧ AllTreeKeysGood t.right groupId tr
:= by
  obtain ⟨_, ⟨⟩⟩ := t
  rw [AllTreeKeysGood.eq_def]
  rfl

/-- `AllTreeKeysGood` of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem AllTreeKeysGood_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (groupId: MlsBytes Bytes) (tr: ProofTrace) (li: Nat):
  AllTreeKeysGood t groupId tr ↔
    (nodeNotBlank t → NodeKeyGood tr t groupId) ∧ AllTreeKeysGood (t.child li) groupId tr ∧ AllTreeKeysGood (t.sibling li) groupId tr
:= by
  rw [AllTreeKeysGood_left_right, Tree.child_eq_left_right, Tree.sibling_eq_left_right]
  grind

end Good

/-! ## Proofs -/

/-- The leaves of a node are the leaves of its children. -/
public
theorem leafAt_left_right {Leaf Node: Type} {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  leafAt t li = if li < t.right.position then leafAt t.left li else leafAt t.right li
:= by
  rw [leafAt.eq_def]
  grind

/-- The leaf of a tree of height `0`. -/
public
theorem leafAt_zero {Leaf Node: Type} (t: Tree Leaf Node 0) (li: Nat): leafAt t li = t.leafContent := by
  rw [leafAt.eq_def]
  simp

/-- The leaves of a node are the leaves of its child. -/
public
theorem leafAt_succ {Leaf Node: Type} {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  leafAt t li = leafAt (t.child li) li
:= by
  rw [leafAt.eq_def]
  grind

section Trees

variable [HasSymbolicBytes]

public
theorem getNodeContent_zero (t: TreeSync Bytes tkt 0):
  getNodeContent t = (t.leafContent.map (·.data.content.val)).getD BytesLike.empty
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  cases c <;> rfl

public
theorem getNodeContent_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  getNodeContent t = (t.nodeContent.map (·.content.val)).getD BytesLike.empty
:= by
  obtain ⟨_, bt⟩ := t
  cases bt with | node c L R => cases c <;> rfl

/--
Port of `unmerged_leaf_exists_un_add` (for any predicate).
MLS* requires `x: leaf_index l i` (here `hli`) and `~(mem_ul x excluded_leaves)` (here, the predicate).
-/
theorem leafAt_unAddP {l: Nat} (t: TreeSync Bytes tkt l) (p: Nat → Bool) (li: Nat) (hli: t.containsLeafIndex li):
  leafAt (TreeSync.unAddP t p) li = if p li then leafAt t li else none
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    have := eq_of_containsLeafIndex_zero t.containsLeafIndex_position hli
    grind [leafAt.eq_def, unAddP_zero]
  | node t ih =>
    have := unAddP_succ t li p
    grind [leafAt.eq_def]

theorem containsLeafIndex_of_memUl_unmergedLeavesOf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (hok: unmergedLeavesOk t) (h: memUl li (unmergedLeavesOf t)):
  t.containsLeafIndex li
:= by
  cases l with
  | zero => simp [unmergedLeavesOf_zero, memUl] at h
  | succ l =>
    rw [unmergedLeavesOf_eq] at h
    cases hc: t.nodeContent with
    | none => simp [hc, memUl] at h
    | some content =>
      have := unmergedLeavesOk_content t content hc hok
      grind [memUl_iff]

/-- The leaves of `canonicalizeLeafSignature t c`. -/
theorem leafAt_canonicalizeLeafSignature {l: Nat} (t: TreeSync Bytes tkt l) (c li: Nat)
  (hc: t.containsLeafIndex c) (hli: t.containsLeafIndex li):
  leafAt (canonicalizeLeafSignature t c) li =
    if c = li then (leafAt t li).map fun ln => { ln with signature := MlsBytes.empty } else leafAt t li
:= by
  induction t, hc, hli using Tree.commonPathInduction c li with
  | leaf t => grind [leafAt.eq_def, leafContent_canonicalizeLeafSignature]
  | sameChild t _ ih =>
    have := canonicalizeLeafSignature_succ t c
    grind [leafAt.eq_def]
  | @sibling _ t _ hli' h _ =>
    have := canonicalizeLeafSignature_succ t c
    have := Tree.child_eq_sibling_of_mem_sibling (canonicalizeLeafSignature t c) (li := c) (li' := li) (by grind)
    rw [leafAt_succ _ li, leafAt_succ t li]
    grind

theorem unmergedLeavesOf_canonicalize {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat):
  unmergedLeavesOf (canonicalize t li) = []
:= by
  cases l with
  | zero => grind [unmergedLeavesOf_zero]
  | succ l =>
    have := (canonicalize_succ t li).2.1
    rw [unmergedLeavesOf_eq]
    cases h: (canonicalize t li).nodeContent <;> cases h': t.nodeContent <;> simp_all

/-- Port of `canonicalize_preserves_node_content`. MLS* requires `node_not_blank t`, which is not needed. -/
theorem getNodeContent_canonicalize {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat):
  nodeNotBlank (canonicalize t li) = nodeNotBlank t ∧
  getNodeContent (canonicalize t li) = getNodeContent t
:= by
  cases l with
  | zero =>
    simp only [nodeNotBlank_zero, getNodeContent_zero, leafContent_canonicalize]
    cases t.leafContent <;> simp
  | succ l =>
    have := (canonicalize_succ t li).1
    rw [nodeNotBlank_succ, nodeNotBlank_succ, getNodeContent_succ, getNodeContent_succ]
    cases h: (canonicalize t li).nodeContent <;> cases h': t.nodeContent <;> simp_all

/-! ### Authentifier -/

/--
Port of `tree_list_is_parent_hash_linkedP_unmerged_leaves_eq` (the part on the unmerged leaves;
the subtree part is `treeListIsParentHashLinkedP_head_isSubtreeOf_last`).
MLS* requires `Cons? tl` (here `hx` and `hy`).
-/
theorem memUl_unmergedLeavesOf_head_iff (tl: TreeSyncList Bytes tkt) (x y: OneTreeSync Bytes tkt) (li: Nat)
  (h: TreeListIsParentHashLinkedP tl) (hx: tl.head? = some x) (hy: tl.getLast? = some y) (hok: unmergedLeavesOk y.2):
  memUl li (unmergedLeavesOf x.2) ↔ memUl li (unmergedLeavesOf y.2) ∧ x.2.containsLeafIndex li
:= by
  induction tl generalizing x with
  | nil => exfalso; grind
  | cons a tail ih =>
    obtain rfl: a = x := by simpa using hx
    rcases tail with _ | ⟨b, tail⟩
    · obtain rfl: a = y := by simpa using hy
      grind [containsLeafIndex_of_memUl_unmergedLeavesOf]
    · simp only [TreeListIsParentHashLinkedP, ListChain] at h
      have := ih b h.2 rfl (by simpa using hy)
      obtain ⟨la, a⟩ := a
      obtain ⟨_ | lb, b⟩ := b
      · exfalso; grind [TreeParentHashLinkedP]
      · obtain ⟨hl, ⟨hsub, hlinked⟩, hokb⟩ := h.1
        have := memUl_unmergedLeavesOf_iff a b li (TreeParentHashLinkedP.nodeHasParentHash h.1) hsub hl
          (by grind [parentHashLinked]) hokb
        grind


/--
Port of `authentifier_index_is_not_unmerged` (the unmerged leaves part).
MLS*'s `get_authentifier_index t` is any leaf index satisfying `IsAuthentifierIndex`.
MLS* also requires `parent_hash_invariant t` and `node_has_parent_hash t`, only needed for the existence of the authentifier.
-/
theorem _root_.MLS.TreeSync.IsAuthentifierIndex.not_memUl {l: Nat} {t: TreeSync Bytes tkt l} {li: Nat}
  (h: IsAuthentifierIndex t li) (hok: unmergedLeavesOk t):
  ¬ memUl li (unmergedLeavesOf t)
:= by
  obtain ⟨tl, leaf, hlinked, hlast, hhead, rfl⟩ := h
  have := memUl_unmergedLeavesOf_head_iff tl _ _ leaf.position hlinked hhead hlast hok
  grind [unmergedLeavesOf_zero, memUl]

/-- Port of `authentifier_index_is_not_unmerged` (the source part): the authentifier leaf is a leaf of a commit. -/
theorem _root_.MLS.TreeSync.IsAuthentifierIndex.source_eq_commit {l: Nat} {t: TreeSync Bytes tkt l} {li: Nat} {ln: LeafNode Bytes tkt}
  (h: IsAuthentifierIndex t li) (hph: nodeHasParentHash t) (hln: leafAt t li = some ln):
  ln.data.source = .commit
:= by
  obtain ⟨tl, leaf, hlinked, hlast, hhead, rfl⟩ := h
  have hsub := treeListIsParentHashLinkedP_head_isSubtreeOf_last tl _ _ hlinked hhead hlast
  have := treeListIsParentHashLinkedP_head_nodeHasParentHash tl _ _ hlinked hhead hlast hph
  have := leafAt_of_isSubtreeOf_zero leaf t hsub
  grind [nodeHasParentHash, getParentHashOf_leaf]

/--
Port of `authentifier_index_is_in_canonicalization`.
MLS* also requires `parent_hash_invariant t`, only needed for the existence of the authentifier.
-/
theorem _root_.MLS.TreeSync.IsAuthentifierIndex.leafAt_canonicalizeUnmergedLeaves {l: Nat} {t: TreeSync Bytes tkt l} {li: Nat}
  (h: IsAuthentifierIndex t li) (hok: unmergedLeavesOk t) (hph: nodeHasParentHash t):
  leafAt (canonicalizeUnmergedLeaves t) li = leafAt t li
:= by
  rw [canonicalizeUnmergedLeaves, TreeSync.unAdd, leafAt_unAddP t _ li (h.leafAt hph).1]
  simp [unAddUnmergedLeaf, h.not_memUl hok]

@[simp]
theorem canonicalizeUnmergedLeaves_position {l: Nat} (t: TreeSync Bytes tkt l):
  (canonicalizeUnmergedLeaves t).position = t.position
:= by
  simp [canonicalizeUnmergedLeaves, TreeSync.unAdd]

grind_pattern canonicalizeUnmergedLeaves_position => (canonicalizeUnmergedLeaves t).position

/-- The leaves of `canonicalizeUnmergedLeaves` of a leaf. -/
public
theorem canonicalizeUnmergedLeaves_zero (t: TreeSync Bytes tkt 0): canonicalizeUnmergedLeaves t = t := by
  rw [canonicalizeUnmergedLeaves, unmergedLeavesOf_zero, unAdd_nil]

/-- The node content of a well-formed tree satisfies the predicate. -/
theorem getNodeContent_wf {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred] (t: TreeSync Bytes tkt l)
  (hwf: (TreeSync.mf tkt l).wf pred t):
  pred (getNodeContent t)
:= by
  cases l with
  | zero =>
    rw [Tree.mf.wf_zero] at hwf
    rw [getNodeContent_zero]
    cases h: t.leafContent <;> simp_all [BytesCompatiblePred.pred_empty]
  | succ l =>
    rw [Tree.mf.wf_succ] at hwf
    rw [getNodeContent_succ]
    cases h: t.nodeContent <;> simp_all [BytesCompatiblePred.pred_empty]

end Trees

section Lemmas

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

public
theorem nodeSkLabelAux_zero (t: TreeSync Bytes tkt 0) (groupId: MlsBytes Bytes) (ty: NodeLabelType):
  nodeSkLabelAux t groupId ty = (t.leafContent.map (nodeSkLabelAuxLeaf · groupId ty t.position)).getD Label.secret
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  rw [nodeSkLabelAux.eq_def]
  cases c <;> rfl

public
theorem nodeSkLabelAux_left_right {l: Nat} (t: TreeSync Bytes tkt (l+1)) (groupId: MlsBytes Bytes) (ty: NodeLabelType):
  nodeSkLabelAux t groupId ty = (nodeSkLabelAux t.left groupId ty).join (nodeSkLabelAux t.right groupId ty)
:= by
  obtain ⟨_, ⟨⟩⟩ := t
  rw [nodeSkLabelAux.eq_def]
  rfl

/--
The label of the node keys of a tree is corrupt when the label of one of its leaves is.
This characterization replaces MLS*'s inductions on the tree in the lemmas comparing the labels of trees.
-/
public
theorem nodeSkLabelAux_isCorrupt {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (ty: NodeLabelType)
  (tr: ExecTrace):
  (nodeSkLabelAux t groupId ty).isCorrupt tr ↔
    ∃ li ln, t.containsLeafIndex li ∧ leafAt t li = some ln ∧ (nodeSkLabelAuxLeaf ln groupId ty li).isCorrupt tr
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    rw [nodeSkLabelAux_zero]
    cases h: t.leafContent <;> grind [leafAt.eq_def, Tree.containsLeafIndex]
  | node t ihl ihr =>
    rw [nodeSkLabelAux_left_right, Label.joinIsCorrupt, ihl, ihr]
    grind [leafAt_left_right, Tree.containsLeafIndex, Tree.right_position, Tree.left_position]

/-- The label of the node keys of `t1` flows to the one of `t2` when it does on each leaf of `t2`. -/
public
theorem nodeSkLabelAux_canFlow {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2)
  (groupId1 groupId2: MlsBytes Bytes) (ty1 ty2: NodeLabelType) (tr: ExecTrace)
  (h: ∀ li ln2, t2.containsLeafIndex li → leafAt t2 li = some ln2 →
    ∃ ln1, t1.containsLeafIndex li ∧ leafAt t1 li = some ln1 ∧
      (nodeSkLabelAuxLeaf ln1 groupId1 ty1 li).canFlow (nodeSkLabelAuxLeaf ln2 groupId2 ty2 li) tr):
  (nodeSkLabelAux t1 groupId1 ty1).canFlow (nodeSkLabelAux t2 groupId2 ty2) tr
:= by
  intro trLater hle h2
  rw [nodeSkLabelAux_isCorrupt] at h2 ⊢
  grind [Label.canFlow]

/-- `nodeSkLabelAux` of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem nodeSkLabelAux_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (groupId: MlsBytes Bytes) (ty: NodeLabelType) (li: Nat):
  nodeSkLabelAux t groupId ty = (nodeSkLabelAux (t.child li) groupId ty).join (nodeSkLabelAux (t.sibling li) groupId ty)
:= by
  rw [nodeSkLabelAux_left_right, Tree.child_eq_left_right, Tree.sibling_eq_left_right]
  grind

/-- Two trees whose leaves have the same labels have the same node keys label. -/
public
theorem nodeSkLabelAux_eq {l: Nat} (t1 t2: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (ty1 ty2: NodeLabelType)
  (hpos: t1.position = t2.position)
  (h: ∀ li, t1.containsLeafIndex li →
    (leafAt t1 li).map (nodeSkLabelAuxLeaf · groupId ty1 li) = (leafAt t2 li).map (nodeSkLabelAuxLeaf · groupId ty2 li)):
  nodeSkLabelAux t1 groupId ty1 = nodeSkLabelAux t2 groupId ty2
:= by
  apply Label.ext
  intro tr
  apply propext
  rw [nodeSkLabelAux_isCorrupt, nodeSkLabelAux_isCorrupt]
  have: ∀ li, t1.containsLeafIndex li ↔ t2.containsLeafIndex li := by grind [Tree.containsLeafIndex]
  grind [Option.map_eq_some_iff]

/-! ### Labels of leaves -/

public
theorem nodeSkLabelAuxLeaf_noCommitter_self (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (i: Nat):
  nodeSkLabelAuxLeaf ln groupId (.noCommitter i) i = Label.secret
:= by
  simp [nodeSkLabelAuxLeaf]

/-- Away from the committer, the labels of leaves do not depend on the committer. -/
public
theorem nodeSkLabelAuxLeaf_of_ne (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li i: Nat) (h: i ≠ li):
  nodeSkLabelAuxLeaf ln groupId (.noCommitter li) i = nodeSkLabelAuxLeaf ln groupId .yesCommitter i ∧
  nodeSkLabelAuxLeaf ln groupId (.noCommitterSignature li) i = nodeSkLabelAuxLeaf ln groupId .yesCommitter i
:= by
  simp [nodeSkLabelAuxLeaf, Ne.symm h]

theorem nodeSkLabelAuxLeaf_canFlow_nosig (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li i: Nat) (tr: ExecTrace):
  (nodeSkLabelAuxLeaf ln groupId .yesCommitter i).canFlow (nodeSkLabelAuxLeaf ln groupId (.noCommitterSignature li) i) tr
:= by
  by_cases h: i = li
  · -- on the committer's leaf, the signature label is replaced by `secret`
    subst h
    simp only [nodeSkLabelAuxLeaf, reduceCtorEq, ite_true, ite_false]
    split <;> (try split) <;> grind [Label.canFlow]
  · rw [(nodeSkLabelAuxLeaf_of_ne _ _ _ _ h).2]
    exact canFlowRefl _ _

/-- The label of a leaf contains its guarded signature key label. -/
theorem nodeSkLabelAuxLeaf_isCorrupt_of_guardedSignatureKeyLabel (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes)
  (i: Nat) (tr: ExecTrace) (h: (guardedSignatureKeyLabel ln groupId i).isCorrupt tr):
  (nodeSkLabelAuxLeaf ln groupId .yesCommitter i).isCorrupt tr
:= by
  unfold nodeSkLabelAuxLeaf guardedSignatureKeyLabel at *
  split at h <;> grind

/-- The label of the committer's leaf without signature does not depend on the signature, except for key packages. -/
theorem nodeSkLabelAuxLeaf_nosig_signature (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (i: Nat) (signature: MlsBytes Bytes)
  (hsrc: ln.data.source ≠ .keyPackage):
  nodeSkLabelAuxLeaf { ln with signature } groupId (.noCommitterSignature i) i = nodeSkLabelAuxLeaf ln groupId (.noCommitterSignature i) i
:= by
  unfold nodeSkLabelAuxLeaf
  grind

/-- The label of the key package leaf without signature flows to the node key label of the principal of the leaf. -/
theorem nodeSkLabelAuxLeaf_keyPackage_canFlow (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat) (prin: Participant)
  (tr: ExecTrace) (hcp: credentialToPrincipal ln.data.credential = some prin) (hsrc: ln.data.source = .keyPackage):
  (nodeSkLabelAuxLeaf ln groupId (.noCommitterSignature li) li).canFlow (nodeKeyLabel prin ln.data.content.val) tr
:= by
  simp only [nodeSkLabelAuxLeaf, reduceCtorEq, hcp, hsrc]
  grind [Label.canFlow]

/-! ### Labels of trees -/

/--
Port of `node_sk_label_aux_flows_to_node_sk_label_aux_leaf`.
MLS* requires `li: leaf_index l i` (here `hli`); MLS*'s `match leaf_at t li` is the hypothesis `hln`
(on blank leaves, the label is `secret`, to which every label flows).
-/
public
theorem nodeSkLabelAux_canFlow_leaf {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (ty: NodeLabelType)
  (li: Nat) (ln: LeafNode Bytes tkt) (tr: ExecTrace)
  (hli: t.containsLeafIndex li) (hln: leafAt t li = some ln):
  (nodeSkLabelAux t groupId ty).canFlow (nodeSkLabelAuxLeaf ln groupId ty li) tr
:= by
  intro _ _ h
  grind [nodeSkLabelAux_isCorrupt]

/-- Port of `node_sk_label_flows_to_node_sk_label_nosig`. -/
public
theorem nodeSkLabel_canFlow_nodeSkLabelNosig {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (committerLeafIndex: Nat) (tr: ExecTrace):
  (nodeSkLabel t groupId).canFlow (nodeSkLabelNosig t groupId committerLeafIndex) tr
:= by
  apply nodeSkLabelAux_canFlow
  grind [nodeSkLabelAuxLeaf_canFlow_nosig]

/-- Port of `node_sk_label_flows_to_node_sk_label_without_committer`. -/
public
theorem nodeSkLabelCanon_canFlow_nodeSkLabelCanonNosig {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (committerLeafIndex: Nat) (tr: ExecTrace):
  (nodeSkLabelCanon t groupId).canFlow (nodeSkLabelCanonNosig t groupId committerLeafIndex) tr
:=
  nodeSkLabel_canFlow_nodeSkLabelNosig (canonicalizeUnmergedLeaves t) groupId committerLeafIndex tr

/-- Port of `node_sk_label_flows_to_un_addP`. -/
theorem nodeSkLabel_canFlow_unAddP {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (p: Nat → Bool)
  (tr: ExecTrace):
  (nodeSkLabel t groupId).canFlow (nodeSkLabel (TreeSync.unAddP t p) groupId) tr
:= by
  apply nodeSkLabelAux_canFlow
  intro li ln hli hln
  have hli': t.containsLeafIndex li := by simpa [Tree.containsLeafIndex] using hli
  grind [leafAt_unAddP]

/-- Port of `node_sk_label_flows_to_node_sk_label_canon`. -/
public
theorem nodeSkLabel_canFlow_nodeSkLabelCanon {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (tr: ExecTrace):
  (nodeSkLabel t groupId).canFlow (nodeSkLabelCanon t groupId) tr
:=
  nodeSkLabel_canFlow_unAddP t groupId _ tr

/-- Port of `node_sk_label_noX_eq_node_sk_label`. -/
public
theorem nodeSkLabel_eq_of_not_mem {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat)
  (h: ¬ t.containsLeafIndex li):
  nodeSkLabel t groupId = nodeSkLabelNosig t groupId li ∧
  nodeSkLabel t groupId = nodeSkLabelNocommitter t groupId li
:= by
  constructor <;> apply nodeSkLabelAux_eq _ _ _ _ _ rfl <;> intro i hi <;>
    simp [nodeSkLabelAuxLeaf_of_ne _ _ _ _ (show i ≠ li by grind)]

/-- Port of `node_sk_label_aux_empty`. -/
public
theorem nodeSkLabelAux_of_isTreeEmpty {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (ty: NodeLabelType)
  (h: isTreeEmpty t):
  nodeSkLabelAux t groupId ty = Label.secret
:= by
  apply Label.ext
  intro tr
  rw [nodeSkLabelAux_isCorrupt]
  grind [leafAt_of_isTreeEmpty]

/-- Port of `node_sk_label_nocommitter_empty`. -/
public
theorem nodeSkLabelNocommitter_of_isTreeEmpty {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat)
  (h: isTreeEmpty t):
  nodeSkLabelNocommitter t groupId li = Label.secret
:=
  nodeSkLabelAux_of_isTreeEmpty t groupId _ h

/-- Port of `node_sk_label_nosig_join_node_sk_label_nocommitter_eq`. -/
public
theorem nodeSkLabelNocommitter_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (groupId: MlsBytes Bytes) (li: Nat):
  (nodeSkLabelNocommitter (t.child li) groupId li).join (nodeSkLabelNosig (t.sibling li) groupId li) =
    nodeSkLabelNocommitter t groupId li
:= by
  have := nodeSkLabel_eq_of_not_mem (t.sibling li) groupId li (Tree.not_mem_sibling_self _ _)
  simp only [nodeSkLabelNocommitter] at this ⊢
  rw [← this.1, this.2, nodeSkLabelAux_succ t groupId (.noCommitter li) li]

/-! ### Canonicalization -/

/--
Port of `canonicalize_preserves_node_sk_label_nosig`.
MLS* requires `committer_leaf_index: leaf_index l i` (here `hc`) and `Some? (leaf_at t committer_leaf_index)`
with source `LNS_commit` (here `hln` and `hsrc`, for any source but `LNS_key_package`).
-/
theorem nodeSkLabelNosig_canonicalizeLeafSignature {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (c: Nat) (ln: LeafNode Bytes tkt)
  (hc: t.containsLeafIndex c) (hln: leafAt t c = some ln) (hsrc: ln.data.source ≠ .keyPackage):
  nodeSkLabelNosig (canonicalizeLeafSignature t c) groupId c = nodeSkLabelNosig t groupId c
:= by
  apply nodeSkLabelAux_eq _ _ _ _ _ (canonicalizeLeafSignature_position t c)
  intro li hli
  have hli' := Tree.containsLeafIndex_of_position_eq _ t li (canonicalizeLeafSignature_position t c) hli
  rw [leafAt_canonicalizeLeafSignature t c li hc hli']
  split
  · subst c
    simp [hln, nodeSkLabelAuxLeaf_nosig_signature _ _ _ _ hsrc]
  · rfl

/--
Port of `canonicalize_preserves_node_sk_label_without_committer`.
MLS* requires `li: leaf_index l i` (here `hli`) and `Some? (leaf_at (canonicalize_unmerged_leaves t) li)`
with source `LNS_commit` (here `hln` and `hsrc`, for any source but `LNS_key_package`).
-/
theorem nodeSkLabelCanonNosig_canonicalize {l: Nat} (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (li: Nat) (ln: LeafNode Bytes tkt)
  (hli: t.containsLeafIndex li) (hln: leafAt (canonicalizeUnmergedLeaves t) li = some ln)
  (hsrc: ln.data.source ≠ .keyPackage):
  nodeSkLabelCanonNosig (canonicalize t li) groupId li = nodeSkLabelCanonNosig t groupId li
:= by
  have: canonicalizeUnmergedLeaves (canonicalize t li) = canonicalize t li :=
    canonicalizeUnmergedLeaves_eq_self _ (by simp [isUnmergedLeavesCanonicalized, unmergedLeavesOf_canonicalize])
  rw [nodeSkLabelCanonNosig, this, canonicalize]
  apply nodeSkLabelNosig_canonicalizeLeafSignature _ _ _ ln _ hln hsrc
  exact Tree.containsLeafIndex_of_position_eq t _ li (by simp [canonicalizeUnmergedLeaves, TreeSync.unAdd]) hli

end Lemmas

section NodeKeyGoodNosig

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/--
`NodeKeyGood` without the invariant of the node content (which follows from the well-formedness of the tree):
the conclusion of `all_tree_keys_good_parent_hash_case` and of the leaf cases.
-/
def NodeKeyLabelGood {l: Nat} (tr: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Prop :=
  (nodeSkLabelCanon t groupId).canFlow ((getNodeContent t).hpkeSkLabel tr) tr.erase ∧ (
    (
      (getNodeContent t).HpkeSkHasUsage nodeKeyUsage tr ∧
      ((1 ≤ l ∧ getParentHashOf t = some rootParentHash) → IsRootNodePk tr (getNodeContent t))
    ) ∨ (
      (nodeSkLabelCanon t groupId).canFlow Label.pub tr.erase
    )
  )

theorem NodeKeyGood_iff {l: Nat} (tr: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes):
  NodeKeyGood tr t groupId ↔ (getNodeContent t).Invariant tr ∧ NodeKeyLabelGood tr t groupId
:= Iff.rfl

/--
The node key properties given by the event predicate of `GroupHasTreeEvent` (without `nodeNotBlank`),
i.e. MLS*'s authentication predicate in `all_tree_keys_good_parent_hash_case` and the leaf cases.
-/
def NodeKeyGoodNosig {l: Nat} (tr: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat): Prop :=
  (getNodeContent t).Invariant tr ∧
  (nodeSkLabelCanonNosig t groupId li).canFlow ((getNodeContent t).hpkeSkLabel tr) tr.erase ∧
  (getNodeContent t).HpkeSkHasUsage nodeKeyUsage tr ∧
  ((1 ≤ l ∧ getParentHashOf t = some rootParentHash) → IsRootNodePk tr (getNodeContent t))

theorem NodeKeyGoodNosig_later {l: Nat} (tr1 tr2: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat)
  : tr1 ≤ tr2 →
    NodeKeyGoodNosig tr1 t groupId li →
    NodeKeyGoodNosig tr2 t groupId li
:= by
  grind [NodeKeyGoodNosig]

grind_pattern NodeKeyGoodNosig_later => tr1 ≤ tr2, NodeKeyGoodNosig tr1 t groupId li
grind_pattern [grind_later] NodeKeyGoodNosig_later => tr1 ≤ tr2, NodeKeyGoodNosig tr1 t groupId li

/-- The node key properties of a tree follow from the ones of its canonicalization. -/
theorem NodeKeyGoodNosig_of_canonicalize {l: Nat} (tr: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (li: Nat) (ln: LeafNode Bytes tkt)
  (hli: t.containsLeafIndex li) (hln: leafAt (canonicalizeUnmergedLeaves t) li = some ln)
  (hsrc: ln.data.source ≠ .keyPackage) (h: NodeKeyGoodNosig tr (canonicalize t li) groupId li):
  NodeKeyGoodNosig tr t groupId li
:= by
  have := (getNodeContent_canonicalize t li).2
  have := nodeSkLabelCanonNosig_canonicalize t groupId li ln hli hln hsrc
  grind [NodeKeyGoodNosig, getParentHashOf_canonicalize]

/-- When the label of the node keys of a tree is corrupt, `NodeKeyLabelGood` holds. -/
theorem NodeKeyLabelGood_of_isCorrupt {l: Nat} (tr: ProofTrace) (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (h: (nodeSkLabelCanon t groupId).isCorrupt tr.erase):
  NodeKeyLabelGood tr t groupId
:= by
  grind [NodeKeyLabelGood, Label.canFlow_of_isCorrupt]

/-- The node key properties without the committer's signature, on a prefix of the trace, imply `NodeKeyLabelGood`. -/
theorem NodeKeyLabelGood_of_NodeKeyGoodNosig {l: Nat} (trBefore tr: ProofTrace) (t: TreeSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (li: Nat) (hle: trBefore ≤ tr) (h: NodeKeyGoodNosig trBefore t groupId li):
  NodeKeyLabelGood tr t groupId
:= by
  have := nodeSkLabelCanon_canFlow_nodeSkLabelCanonNosig t groupId li tr.erase
  have: NodeKeyGoodNosig tr t groupId li := by grind
  grind [NodeKeyGoodNosig, NodeKeyLabelGood, canFlowTrans]

end NodeKeyGoodNosig

section Proofs

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]
variable [HasTreesyncTreekemLinkInvariants]

/-- The principal of a verified leaf node exists (the AS validated its credential, by the event predicate). -/
theorem exists_credentialToPrincipal (tr: ProofTrace) (me: Participant)
  (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat)
  (hev: IHaveVerifiedLeafNode tr.erase me ln groupId li) (hinv: tr.Invariant):
  ∃ prin, credentialToPrincipal ln.data.credential = some prin
:= by
  obtain ⟨i, -, -, ⟨token, hcred⟩, -⟩ := ProtocolEvent.EventInv.Has.pred_of_eventLogged leafNodeHasBeenVerifiedPred tr _ hinv hev
  obtain ⟨prin, hprin, -⟩ := isSignatureKeyVk_of_credentialOk _ _ _ token hcred
  grind

/--
Port of `guarded_authentication_lemma`, for the guarded signature key label of a leaf node verified by `me`:
either the signature key of the leaf was corrupt before the leaf node was verified,
or an authentication predicate holds before, when it follows from the event predicate of the verification
(unless the signature key was corrupt).
-/
theorem guardedAuthentication_leafNodeHasBeenVerified (tr: ProofTrace) (me: Participant)
  (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat) (authPred: ProofTrace → Prop)
  (hauth: ∀ i p, leafNodeHasBeenVerifiedPred (tr.prefix i) ({ prin := p, leafNode := ln, groupId, leafIndex := li }: LeafNodeHasBeenVerified tkt) →
    ∃ prin, credentialToPrincipal ln.data.credential = some prin ∧ (
      authPred (tr.prefix i) ∨ (signatureKeyLabel prin ln.data.signatureKey.val).isCorrupt (tr.prefix i).erase
    ))
  (hev: IHaveVerifiedLeafNode tr.erase me ln groupId li) (hinv: tr.Invariant):
  (guardedSignatureKeyLabel ln groupId li).isCorrupt tr.erase ∨ ∃ i, authPred (tr.prefix i)
:= by
  obtain ⟨prin, hcp⟩ := exists_credentialToPrincipal tr me ln groupId li hev hinv
  simp only [guardedSignatureKeyLabel, hcp]
  refine (Label.guarded_authentication tr _ _ authPred ?_ ?_ ?_).imp_right fun ⟨i, _, hi⟩ => ⟨i, hi⟩
  all_goals simp only [leafNodeHasBeenVerifiedLabel_isCorrupt, Trace.prefix_erase, not_exists]
  · -- the label becomes corrupt when a principal `p` verifies the leaf node: the event predicate holds before
    intro i ⟨p, hp⟩ hng
    have := ProtocolEvent.eventLoggedAt_of_prefix_succ tr.erase _ i hp (hng p)
    obtain ⟨prin', hcp', h⟩ :=
      hauth i p (ProtocolEvent.EventInv.Has.pred_of_eventLoggedAt leafNodeHasBeenVerifiedPred tr _ i hinv this)
    obtain rfl: prin' = prin := by simp_all
    simpa only [Trace.prefix_erase] using h.symm
  · exact fun p => ProtocolEvent.not_eventLogged_prefix_zero _ _
  · exact ⟨me, hev⟩

/--
The common part of `all_tree_keys_good_parent_hash_case`, `all_tree_keys_good_leaf_node_update_case`
and `all_tree_keys_good_leaf_node_key_package_case`.
The leaf node `ln`, at the leaf `li` of the canonicalized tree, was verified by `me`.
By the guarded authentication lemma, either:
- the signature key of `ln` was corrupt before the verification:
  then the label of the tree, which contains the guarded signature key label of `ln`, is corrupt;
- or the authentication predicate `hauth` held before the verification:
  the node key properties without the signature of the committer (`NodeKeyGoodNosig`).
-/
theorem NodeKeyLabelGood_of_authentication {l: Nat} (tr: ProofTrace) (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat) (ln: LeafNode Bytes tkt)
  (hauth: ∀ i p, leafNodeHasBeenVerifiedPred (tr.prefix i) ({ prin := p, leafNode := ln, groupId, leafIndex := li }: LeafNodeHasBeenVerified tkt) →
    ∃ prin, credentialToPrincipal ln.data.credential = some prin ∧ (
      NodeKeyGoodNosig (tr.prefix i) t groupId li ∨
      (signatureKeyLabel prin ln.data.signatureKey.val).isCorrupt (tr.prefix i).erase
    ))
  (hli: t.containsLeafIndex li) (hln: leafAt (canonicalizeUnmergedLeaves t) li = some ln)
  (hev: IHaveVerifiedLeafNode tr.erase me ln groupId li) (hinv: tr.Invariant):
  NodeKeyLabelGood tr t groupId
:= by
  rcases guardedAuthentication_leafNodeHasBeenVerified tr me ln groupId li
    (NodeKeyGoodNosig · t groupId li) hauth hev hinv with hg | ⟨i, hi⟩
  · -- the signature key of `ln` was corrupt before the verification
    apply NodeKeyLabelGood_of_isCorrupt
    apply nodeSkLabelAux_canFlow_leaf _ groupId _ li ln tr.erase
      (Tree.containsLeafIndex_of_position_eq t _ li (by simp) hli) hln _ (Trace.le_refl _)
    exact nodeSkLabelAuxLeaf_isCorrupt_of_guardedSignatureKeyLabel ln groupId li tr.erase hg
  · -- the node key properties held before the verification
    exact NodeKeyLabelGood_of_NodeKeyGoodNosig _ tr t groupId li (Trace.prefix_le_self _ _) hi

/-- A `GroupHasTreeEvent` on the canonicalization of `t` gives the node key properties of `t`, by its event predicate. -/
theorem NodeKeyGoodNosig_of_treeHasEvent {l: Nat} (tr: ProofTrace) (i: Nat) (prin: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (li: Nat) (ln: LeafNode Bytes tkt)
  (hev: TreeHasEvent prin (tr.prefix i).erase groupId li ⟨l, canonicalize t li⟩)
  (hli: t.containsLeafIndex li) (hln: leafAt (canonicalizeUnmergedLeaves t) li = some ln)
  (hsrc: ln.data.source ≠ .keyPackage) (hinv: tr.Invariant):
  NodeKeyGoodNosig (tr.prefix i) t groupId li
:= by
  obtain ⟨j, hj, hpred⟩ := ProtocolEvent.EventInv.Has.pred_of_eventLogged_prefix groupHasTreeEventPred tr _ i hinv hev
  have: NodeKeyGoodNosig (tr.prefix j) t groupId li := NodeKeyGoodNosig_of_canonicalize _ _ _ _ _ hli hln hsrc hpred.2
  have := Trace.prefix_le_prefix tr j i (by omega)
  grind

/--
Port of `all_tree_keys_good_parent_hash_case`.
MLS*'s `get_authentifier_index t` is any leaf index `authentifierLi` satisfying `IsAuthentifierIndex`.
MLS* also requires `parent_hash_invariant t` (only needed for the existence of the authentifier),
`all_credentials_ok t ast` (only needed for the existence of the principal of the authentifier),
the well-formedness of the authentifier leaf node and `bytes_invariant tr group_id`:
they follow from the event predicate of the verification of the authentifier leaf node.
-/
theorem allTreeKeysGood_parentHashCase {l: Nat} (tr: ProofTrace) (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes) (authentifierLi: Nat)
  (hverif: IHaveVerifiedEveryLeafNode tr.erase me t groupId) (hph: nodeHasParentHash t)
  (hauth: IsAuthentifierIndex t authentifierLi) (hok: unmergedLeavesOk t) (hvalid: validLeavesInvariant groupId t)
  (hinv: tr.Invariant):
  NodeKeyLabelGood tr t groupId
:= by
  obtain ⟨hli, hsome⟩ := hauth.leafAt hph
  obtain ⟨authLn, hln⟩ := Option.isSome_iff_exists.mp hsome
  have hsrc := hauth.source_eq_commit hph hln
  have hlnc := hauth.leafAt_canonicalizeUnmergedLeaves hok hph
  refine NodeKeyLabelGood_of_authentication tr me t groupId authentifierLi authLn ?_ hli (hlnc ▸ hln)
    (IHaveVerifiedLeafNode_of_leafAt _ _ _ _ _ _ hverif hli hln) hinv
  rintro i p ⟨hgroupId, hwf, ⟨token, hcred⟩, -⟩
  obtain ⟨authentifier, hcp, hor⟩ := parentHashImpliesEvent _ _ _ _ _ token hvalid hph hauth hln hcred hwf hgroupId
  refine ⟨authentifier, hcp, hor.imp_left fun hev => ?_⟩
  exact NodeKeyGoodNosig_of_treeHasEvent tr i authentifier t groupId authentifierLi authLn hev hli (hlnc ▸ hln)
    (by simp [hsrc]) hinv

/--
Port of `all_tree_keys_good_leaf_node_update_case`.
MLS*'s tree `TLeaf (Some ln)` is a tree `t` of height `0` with `t.leafContent = some ln` (here `hln`).
MLS* also requires the well-formedness of `ln` and `bytes_invariant tr group_id`,
which follow from the event predicate of the verification of the leaf node.
-/
theorem allTreeKeysGood_leafNodeUpdateCase (tr: ProofTrace) (me: Participant)
  (t: TreeSync Bytes tkt 0) (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes)
  (hln: t.leafContent = some ln) (hsrc: ln.data.source = .update)
  (hev: IHaveVerifiedLeafNode tr.erase me ln groupId t.position) (hinv: tr.Invariant):
  NodeKeyLabelGood tr t groupId
:= by
  have hlnc: leafAt (canonicalizeUnmergedLeaves t) t.position = some ln := by rwa [canonicalizeUnmergedLeaves_zero, leafAt_zero]
  refine NodeKeyLabelGood_of_authentication tr me t groupId t.position ln ?_ t.containsLeafIndex_position hlnc hev hinv
  rintro i p ⟨hgroupId, hwf, ⟨token, hcred⟩, hvalid⟩
  obtain ⟨prin, hcp, hor⟩ := leafNodeSourceUpdateImpliesEvent _ _ _ _ token hsrc hvalid hcred hwf hgroupId
  have ht: ((ChildSiblingView.leaf (some ln) t.position).pack: TreeSync Bytes tkt 0) = t :=
    Tree.ext_zero (by simp) (by simp [hln])
  rw [ht] at hor
  refine ⟨prin, hcp, hor.imp_left fun hev => ?_⟩
  exact NodeKeyGoodNosig_of_treeHasEvent tr i prin t groupId t.position ln hev t.containsLeafIndex_position hlnc
    (by simp [hsrc]) hinv

/-- A `LeafNodeSignedEvent` on the key package of a leaf gives the node key properties of the leaf, by its event predicate. -/
theorem NodeKeyGoodNosig_of_leafNodeHasEvent (tr: ProofTrace) (i: Nat) (prin: Participant)
  (t: TreeSync Bytes tkt 0) (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes)
  (hev: LeafNodeHasEvent prin (tr.prefix i).erase
    { data := ln.data, groupId := StaticOption.mk MlsBytes.empty, leafIndex := StaticOption.mk 0 })
  (hln: t.leafContent = some ln) (hcp: credentialToPrincipal ln.data.credential = some prin)
  (hsrc: ln.data.source = .keyPackage) (hinv: tr.Invariant):
  NodeKeyGoodNosig (tr.prefix i) t groupId t.position
:= by
  obtain ⟨j, hj, hpred⟩ := ProtocolEvent.EventInv.Has.pred_of_eventLogged_prefix leafNodeSignedEventPred tr _ i hinv hev
  simp only [leafNodeSignedEventPred, hsrc] at hpred
  have: NodeKeyGoodNosig (tr.prefix j) t groupId t.position := by
    have := nodeSkLabelAuxLeaf_keyPackage_canFlow ln groupId t.position prin (tr.prefix j).erase hcp hsrc
    simp only [NodeKeyGoodNosig, nodeSkLabelCanonNosig, canonicalizeUnmergedLeaves_zero, nodeSkLabelAux_zero,
      getNodeContent_zero, hln]
    grind [canFlowTrans]
  have := Trace.prefix_le_prefix tr j i (by omega)
  grind

/--
Port of `all_tree_keys_good_leaf_node_key_package_case`.
MLS*'s tree `TLeaf (Some ln)` is a tree `t` of height `0` with `t.leafContent = some ln` (here `hln`).
MLS* also requires the well-formedness of `ln` and `bytes_invariant tr group_id`,
which follow from the event predicate of the verification of the leaf node.
-/
theorem allTreeKeysGood_leafNodeKeyPackageCase (tr: ProofTrace) (me: Participant)
  (t: TreeSync Bytes tkt 0) (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes)
  (hln: t.leafContent = some ln) (hsrc: ln.data.source = .keyPackage)
  (hev: IHaveVerifiedLeafNode tr.erase me ln groupId t.position) (hinv: tr.Invariant):
  NodeKeyLabelGood tr t groupId
:= by
  have hlnc: leafAt (canonicalizeUnmergedLeaves t) t.position = some ln := by rwa [canonicalizeUnmergedLeaves_zero, leafAt_zero]
  refine NodeKeyLabelGood_of_authentication tr me t groupId t.position ln ?_ t.containsLeafIndex_position hlnc hev hinv
  rintro i p ⟨hgroupId, hwf, ⟨token, hcred⟩, hvalid⟩
  obtain ⟨prin, hcp, hor⟩ := leafNodeSourceKeyPackageImpliesEvent _ _ _ _ token hsrc hvalid hcred hwf hgroupId
  refine ⟨prin, hcp, hor.imp_left fun hev => ?_⟩
  exact NodeKeyGoodNosig_of_leafNodeHasEvent tr i prin t ln groupId hev hln hcp hsrc hinv

/--
The node key of a non-blank node of a tree verified by `me` is good: the induction step of `prove_all_tree_keys_good`.
Nodes with a parent hash (non-blank nodes, and leaves of commits) are authenticated by their authentifier,
the other leaves (updates and key packages) by themselves.
-/
theorem nodeKeyGood_of_IHaveVerifiedEveryLeafNode {l: Nat} (tr: ProofTrace) (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (hverif: IHaveVerifiedEveryLeafNode tr.erase me t groupId)
  (hok: unmergedLeavesOk t) (hph: parentHashInvariant t) (hvalid: validLeavesInvariant groupId t)
  (hwf: (TreeSync.mf tkt l).wf (Bytes.Invariant · tr) t) (hinv: tr.Invariant) (hnb: nodeNotBlank t):
  NodeKeyGood tr t groupId
:= by
  rw [NodeKeyGood_iff]
  refine ⟨getNodeContent_wf _ t hwf, ?_⟩
  by_cases hph': nodeHasParentHash t
  · obtain ⟨li, hli⟩ := exists_isAuthentifierIndex t hok hph hph'
    exact allTreeKeysGood_parentHashCase tr me t groupId li hverif hph' hli hok hvalid hinv
  cases l with
  | succ l =>
    exfalso
    grind [nodeNotBlank_succ, nodeHasParentHash, getParentHashOf_succ]
  | zero =>
    obtain ⟨ln, hln⟩: ∃ ln, t.leafContent = some ln := by simpa [nodeNotBlank_zero, Option.isSome_iff_exists] using hnb
    have hev := IHaveVerifiedLeafNode_of_leafAt _ _ _ _ t.position ln hverif t.containsLeafIndex_position
      (by rwa [leafAt_zero])
    cases hsrc: ln.data.source with
    | keyPackage => exact allTreeKeysGood_leafNodeKeyPackageCase tr me t ln groupId hln hsrc hev hinv
    | update => exact allTreeKeysGood_leafNodeUpdateCase tr me t ln groupId hln hsrc hev hinv
    | commit =>
      exfalso
      simp [nodeHasParentHash, getParentHashOf_leaf _ _ hln, hsrc] at hph'

/--
Port of `prove_all_tree_keys_good`.
MLS* also requires `all_credentials_ok t ast` and `bytes_invariant tr group_id`,
which follow from the event predicates of the verification of the leaf nodes.
-/
public
theorem proveAllTreeKeysGood {l: Nat} (tr: ProofTrace) (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (hverif: IHaveVerifiedEveryLeafNode tr.erase me t groupId)
  (hok: unmergedLeavesOk t) (hph: parentHashInvariant t) (hvalid: validLeavesInvariant groupId t)
  (hwf: (TreeSync.mf tkt l).wf (Bytes.Invariant · tr) t) (hinv: tr.Invariant):
  AllTreeKeysGood t groupId tr
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    grind [AllTreeKeysGood_zero, nodeKeyGood_of_IHaveVerifiedEveryLeafNode]
  | node t ihl ihr =>
    rw [AllTreeKeysGood_left_right]
    have := (IHaveVerifiedEveryLeafNode_succ _ _ _ _ t.position).mp hverif
    rw [Tree.child_position, Tree.sibling_position] at this
    have hsubl: t.left.IsSubtreeOf t := Tree.IsSubtreeOf.of_child (li := t.position) (by grind)
    have hsubr: t.right.IsSubtreeOf t := Tree.IsSubtreeOf.of_child (li := t.right.position) (by grind)
    grind [nodeKeyGood_of_IHaveVerifiedEveryLeafNode, unmergedLeavesOk_of_isSubtreeOf, parentHashInvariant_of_isSubtreeOf,
      validLeavesInvariant_of_isSubtreeOf, wf_of_isSubtreeOf]

end Proofs

end MLS.TreeKEM
