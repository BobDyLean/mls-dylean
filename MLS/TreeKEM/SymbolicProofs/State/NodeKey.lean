module

public import MLS.TreeKEM.SymbolicSpec.State.NodeKey

/-!
Port of the labels, usages and predicates of `MLS.TreeKEM.Symbolic.State.NodeKey`:
the label of the private keys of a path (TreeKEM node keys), and the properties of these keys.

Port-specific differences:
- DY*'s `typed_state_pred_label (node_key_label_pred prin leaf_pk)` is a DyLean label
  whose corruption is the compromise of a node keys state of `prin` whose leaf private key has the public key `leaf_pk`
  (as `MLS.TreeSync.signatureKeyLabel`). Since states are identified by their content (and not their tag, session identifier),
  `node_key_label_pred` is inlined in `nodeKeyLabel`.
- The state invariant (`treekem_node_keys_state_pred`, with `treekem_priv_state_pred_knowable`)
  and the invariant proofs of the traceful functions (`mk_leaf_node_key_proof`, …) are not ported yet.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open DySlop.HPKE
open MLS

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMNodeKeysState)]

/--
Port of `node_key_label` (with `node_key_label_pred`):
the node keys of `prin` whose leaf has the public key `leafPk` are corrupt
when a node keys state of `prin`, whose leaf private key has the public key `leafPk`, is compromised.
-/
@[expose]
public
def nodeKeyLabel (prin: Participant) (leafPk: Bytes): Label where
  isCorrupt tr :=
    ∃ (l: Nat) (path: TreeKEMPriv Bytes l),
      hpkePk path.getPathLeaf = leafPk ∧
      PersistentLocalState.LocalStateCompromised prin ({ l, path }: TreeKEMNodeKeysState) tr

/-- Port of `node_key_label_can_flow_public`. -/
public
theorem nodeKeyLabel_canFlow_pub (tr: ExecTrace) (prin: Participant) (leafPk: Bytes)
  : (nodeKeyLabel prin leafPk).canFlow Label.pub tr →
    ∃ (l: Nat) (path: TreeKEMPriv Bytes l),
      PersistentLocalState.LocalStateCompromised prin ({ l, path }: TreeKEMNodeKeysState) tr ∧
      hpkePk path.getPathLeaf = leafPk
:= by
  rw [← canFlowPubEqIsCorrupt]
  grind [nodeKeyLabel]

end Labels

section Usages

variable [HasSymbolicBytes]

/-- Port of `node_key_usage`. -/
@[expose]
public
def nodeKeyUsage: Usage :=
  mkHpkeSkUsage ("MLS.NodeHpkeKey", BytesLike.empty)

/-- Port of `entropy_usage_for_node_key`. -/
@[expose]
public
def entropyUsageForNodeKey: Usage :=
  mkHpkeEntropyUsage ("MLS.NodeHpkeKey", BytesLike.empty)

end Usages

section Predicates

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMNodeKeysState)]

/-- Port of `is_node_sk_for_leaf_pk`. -/
@[expose]
public
def IsNodeSkForLeafPk (tr: ProofTrace) (prin: Participant) (leafPk nodeSk: Bytes): Prop :=
  nodeSk.Invariant tr ∧
  (nodeSk.label tr).canFlow (nodeKeyLabel prin leafPk) tr.erase ∧
  nodeSk.HasUsage nodeKeyUsage tr

/-- Port of `is_node_pk_for_leaf_pk`. -/
@[expose]
public
def IsNodePkForLeafPk (tr: ProofTrace) (prin: Participant) (leafPk nodePk: Bytes): Prop :=
  nodePk.Invariant tr ∧
  (nodePk.hpkeSkLabel tr).canFlow (nodeKeyLabel prin leafPk) tr.erase ∧
  nodePk.HpkeSkHasUsage nodeKeyUsage tr

/-- Node private keys stay node private keys when the trace grows. -/
public
theorem IsNodeSkForLeafPk_later (tr1 tr2: ProofTrace) (prin: Participant) (leafPk nodeSk: Bytes)
  : tr1 ≤ tr2 →
    IsNodeSkForLeafPk tr1 prin leafPk nodeSk →
    IsNodeSkForLeafPk tr2 prin leafPk nodeSk
:= by
  grind [IsNodeSkForLeafPk]

grind_pattern IsNodeSkForLeafPk_later => tr1 ≤ tr2, IsNodeSkForLeafPk tr1 prin leafPk nodeSk
grind_pattern [grind_later] IsNodeSkForLeafPk_later => tr1 ≤ tr2, IsNodeSkForLeafPk tr1 prin leafPk nodeSk

/-- Port of `treekem_priv_state_pred`. -/
@[expose]
public
def TreekemPrivStatePred (tr: ProofTrace) (prin: Participant): {l: Nat} → TreeKEMPriv Bytes l → Prop
  | _, .leaf leafSk => IsNodeSkForLeafPk tr prin (hpkePk leafSk) leafSk
  | _, p@(.node optNodeSk pNext) =>
    TreekemPrivStatePred tr prin pNext ∧
    ∀ nodeSk ∈ optNodeSk, IsNodeSkForLeafPk tr prin (hpkePk p.getPathLeaf) nodeSk

/-- Port of `treekem_priv_state_pred_later`. -/
public
theorem TreekemPrivStatePred_later {l: Nat} (tr1 tr2: ProofTrace) (prin: Participant) (p: TreeKEMPriv Bytes l)
  : tr1 ≤ tr2 →
    TreekemPrivStatePred tr1 prin p →
    TreekemPrivStatePred tr2 prin p
:= by
  intro hle
  induction p <;> grind [TreekemPrivStatePred]

grind_pattern TreekemPrivStatePred_later => tr1 ≤ tr2, TreekemPrivStatePred tr1 prin p
grind_pattern [grind_later] TreekemPrivStatePred_later => tr1 ≤ tr2, TreekemPrivStatePred tr1 prin p

end Predicates

end MLS.TreeKEM
