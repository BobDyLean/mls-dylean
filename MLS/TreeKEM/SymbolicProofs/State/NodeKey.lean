module

public import MLS.TreeKEM.SymbolicSpec.State.NodeKey
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeKEM.SymbolicSpec.State.NodeKey
import DY.Meta.Step

/-!
Port of the labels, usages, predicates and proofs of `MLS.TreeKEM.Symbolic.State.NodeKey`:
the label of the private keys of a path (TreeKEM node keys), the properties of these keys,
the invariant of node keys states, and the proofs of the traceful functions.

Port-specific differences:
- DY*'s `typed_state_pred_label (node_key_label_pred prin leaf_pk)` is a DyLean label
  whose corruption is the compromise of a node keys state of `prin` whose leaf private key has the public key `leaf_pk`
  (as `MLS.TreeSync.signatureKeyLabel`). Since states are identified by their content (and not their tag, session identifier),
  `node_key_label_pred` is inlined in `nodeKeyLabel`.
- The state predicate (`treekem_node_keys_state_pred`) is the DyLean state invariant `treekemNodeKeysStateInv`
  (an instance, as in DyLean's examples): MLS*'s `has_treekem_node_keys_state_invariant` is not needed.
- The proofs of the traceful functions (`mk_leaf_node_key_proof`, …) are DyLean Hoare triples (instances).
  They assume the proof trace entries of the state, and the trace entries and bytes invariants of randomness
  for `mkLeafNodeKey`. The `tr_out == tr` part of their postconditions is not ported
  (DyLean's Hoare triples do not state that the trace is unchanged).
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

/-- Node public keys stay node public keys when the trace grows. -/
public
theorem IsNodePkForLeafPk_later (tr1 tr2: ProofTrace) (prin: Participant) (leafPk nodePk: Bytes)
  : tr1 ≤ tr2 →
    IsNodePkForLeafPk tr1 prin leafPk nodePk →
    IsNodePkForLeafPk tr2 prin leafPk nodePk
:= by
  grind [IsNodePkForLeafPk]

grind_pattern IsNodePkForLeafPk_later => tr1 ≤ tr2, IsNodePkForLeafPk tr1 prin leafPk nodePk
grind_pattern [grind_later] IsNodePkForLeafPk_later => tr1 ≤ tr2, IsNodePkForLeafPk tr1 prin leafPk nodePk

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

/-- Port of `treekem_priv_state_pred_knowable`. -/
theorem TreekemPrivStatePred_knowable {l: Nat} (tr: ProofTrace) (prin: Participant) (p: TreeKEMPriv Bytes l)
  : TreekemPrivStatePred tr prin p →
    (TreeKEMPriv.mf l).wf (Bytes.KnowableBy (nodeKeyLabel prin (hpkePk p.getPathLeaf)) · tr) p
:= by
  induction p with
  | leaf leafSk =>
    simp [TreekemPrivStatePred, NonExtensibleMessageFormat.slowBytes.wf_eq, Path.getPathLeaf]
    grind [IsNodeSkForLeafPk, Bytes.KnowableBy]
  | node optNodeSk pNext ih =>
    cases optNodeSk <;>
      simp_all [TreekemPrivStatePred, MlsOption.mf.wf_eq, NonExtensibleMessageFormat.slowBytes.wf_eq, Path.getPathLeaf] <;>
      grind [IsNodeSkForLeafPk, Bytes.KnowableBy]

/-- Port of `treekem_node_keys_state_pred`: the invariant of node keys states. -/
public
instance treekemNodeKeysStateInv: PersistentLocalState.CompromisableLocalStateInv TreeKEMNodeKeysState where
  invariant prin st tr := TreekemPrivStatePred tr prin st.path
  invariant_later prin st tr1 tr2 := by
    grind
  invariant_implies_KnowableBy prin st tr h := by
    obtain ⟨l, path⟩ := st
    have hflow: (nodeKeyLabel prin (hpkePk path.getPathLeaf)).canFlow
        (PersistentLocalState.label prin ({ l, path }: TreeKEMNodeKeysState)) tr.erase := by
      simp only [Label.canFlow, nodeKeyLabel]
      grind
    simp only [DY.Comparse.IsWellFormed, DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
      NonExtensibleMessageFormat.toExtensible.wf_eq, TreeKEMNodeKeysState.mf.wf_eq]
    exact wf_knowableBy_canFlow _ _ _ tr path hflow (TreekemPrivStatePred_knowable tr prin path h)

end Predicates

section Proofs

open PersistentLocalState

variable [HasSymbolicInvariants] [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeKEMNodeKeysState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeKEMNodeKeysState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT TreeKEMNodeKeysState)]

/-- Port of `leaf_sk_my_mk_rand_label`. -/
@[expose]
public
def leafSkMyMkRandLabel (me: Participant) (leafSk: Bytes): Label :=
  nodeKeyLabel me (hpkePk leafSk)

/-- Port of `mk_leaf_node_key_proof`. -/
@[instance]
public
theorem mkLeafNodeKey.proof
  [ExecTraceTypes.Has Random.ExecEntryT] [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
  [BytesInvariants.Has DY.Random.invariants]
  (me: Participant):
  HoareTriple
    (mkLeafNodeKey me)
    (fun _ => True)
    (fun (_sid, leafPk) tr =>
      IsNodePkForLeafPk tr me leafPk leafPk ∧
      leafPk.Publishable tr ∧
      (nodeKeyLabel me leafPk).canFlow (leafPk.hpkeSkLabel tr) tr.erase
    )
:= by
  unfold mkLeafNodeKey
  step with ⟨ leafSkMyMkRandLabel me, nodeKeyUsage ⟩
  step_intro
  step by
    simp only [LocalStateInv.invariant]
    grind [TreekemPrivStatePred, IsNodeSkForLeafPk, leafSkMyMkRandLabel]
  step
  grind [IsNodePkForLeafPk, Bytes.Publishable, leafSkMyMkRandLabel, hpkePk.Invariant, hpkePk.label,
    hpkeSkLabel_hpkePk, HpkeSkHasUsage_hpkePk]

/-- Port of `get_node_keys_proof`. -/
@[instance]
public
theorem getNodeKeys.proof {l: Nat} (me: Participant) (sid: Nat):
  HoareTriple
    (getNodeKeys me sid: Traceful (TreeKEMPriv Bytes l))
    (fun _ => True)
    (fun priv tr => TreekemPrivStatePred tr me priv)
:= by
  unfold getNodeKeys
  step
  split
  · step
    simp only [LocalStateInv.invariant] at *
    grind
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

/-- Port of `get_leaf_node_key_proof`. -/
@[instance]
public
theorem getLeafNodeKey.proof (me: Participant) (sid: Nat):
  HoareTriple
    (getLeafNodeKey me sid)
    (fun _ => True)
    (fun leafSk tr => IsNodeSkForLeafPk tr me (hpkePk leafSk) leafSk)
:= by
  unfold getLeafNodeKey
  step
  split
  step
  grind [TreekemPrivStatePred]

/-- Port of `store_node_keys_proof`. -/
@[instance]
public
theorem storeNodeKeys.proof {l: Nat} (me: Participant) (path: TreeKEMPriv Bytes l):
  HoareTriple
    (storeNodeKeys me path)
    (fun tr => TreekemPrivStatePred tr me path)
    (fun _ _ => True)
:= by
  unfold storeNodeKeys
  step by
    simp only [LocalStateInv.invariant]
    grind
  trivial

end Proofs

end MLS.TreeKEM
