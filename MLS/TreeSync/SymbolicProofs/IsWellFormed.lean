module

public import MLS.TreeSync.Code.Parsers
public import MLS.TreeSync.Proofs.ParentHash
public import MLS.TreeSync.Proofs.Operations
public import MLS.Common.Proofs.TreeCommon
public import MLS.Symbolic.Code.Symbolic

/-!
Port of `MLS.TreeSync.Symbolic.IsWellFormed`: well-formedness of the results of the TreeSync operations.

Port-specific differences:
- MLS*'s `pre_*` lemmas (the predicate holds on the bytes computed by a function) are `pred_*`,
  and its `is_well_formed_*` lemmas are `*_wf`; they take the result with a success hypothesis.
- `is_well_formed_tree_truncate` has no hypothesis on the right subtree (truncation drops it).
-/

namespace MLS.TreeSync

open Comparse
open MLS

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `pre_is_hash_compatible`. -/
@[expose]
public
def PreIsHashCompatible (pred: Bytes → Prop): Prop :=
  ∀ b h, pred b → CryptoBytes.hashHash b = .success h → pred h

variable (pred: Bytes → Prop) [BytesCompatiblePred pred]

/-- The children of a well-formed tree are well-formed. -/
public
theorem Tree.mf.wf_child_sibling {Leaf Node: Type}
  (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node)
  {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat)
  (h: (Tree.mf mfLeaf mfNode (l+1)).wf pred t):
  (Tree.mf mfLeaf mfNode l).wf pred (t.child li) ∧ (Tree.mf mfLeaf mfNode l).wf pred (t.sibling li)
:= by
  rw [Tree.mf.wf_succ] at h
  grind

/-- Port of `is_well_formed_tree_change_path`. -/
public
theorem treeChangePath_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (oln: Option (LeafNode Bytes tkt))
  (ht: (TreeSync.mf tkt l).wf pred t) (hln: ∀ ln ∈ oln, (LeafNode.mf tkt).wf pred ln):
  (TreeSync.mf tkt l).wf pred (treeChangePath t li oln none)
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    rw [treeChangePath.eq_def]
    cases oln <;> simp_all [Tree.intoChildSiblingView_zero, MlsOption.mf.wf_eq]
  | node t ih =>
    have := Tree.mf.wf_child_sibling pred _ _ t li ht
    rw [treeChangePath_succ]
    simp [MlsOption.mf.wf_eq]
    grind

/-- Port of `is_well_formed_tree_update`. -/
public
theorem treeUpdate_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (ln: LeafNode Bytes tkt)
  (ht: (TreeSync.mf tkt l).wf pred t) (hln: (LeafNode.mf tkt).wf pred ln):
  (TreeSync.mf tkt l).wf pred (treeUpdate t li ln)
:=
  treeChangePath_wf pred t li (some ln) ht (by simpa using hln)

/-- Port of `is_well_formed_tree_remove`. -/
public
theorem treeRemove_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (ht: (TreeSync.mf tkt l).wf pred t):
  (TreeSync.mf tkt l).wf pred (treeRemove t li)
:=
  treeChangePath_wf pred t li none ht (by simp)

/-- Port of `is_well_formed_mk_blank_tree`. -/
public
theorem mkBlankTree_wf (l p: Nat):
  (TreeSync.mf tkt l).wf pred (mkBlankTree l p)
:= by
  induction l generalizing p <;> simp_all [mkBlankTree, mkBlankTreeGeneral, MlsOption.mf.wf_eq]

/-- Port of `is_well_formed_tree_extend`. -/
public
theorem treeExtend_wf {l: Nat} (t: TreeSync Bytes tkt l)
  (ht: (TreeSync.mf tkt l).wf pred t):
  (TreeSync.mf tkt (l+1)).wf pred (treeExtend t)
:= by
  simp [treeExtend, MlsOption.mf.wf_eq, ht, mkBlankTree_wf]

/-- Port of `is_well_formed_tree_truncate`. -/
public
theorem treeTruncate_wf {l: Nat} (t: TreeSync Bytes tkt (l+1))
  (ht: (TreeSync.mf tkt (l+1)).wf pred t):
  (TreeSync.mf tkt l).wf pred (treeTruncate t)
:= by
  rw [Tree.mf.wf_succ] at ht
  exact ht.2.1

/-- Port of `is_well_formed_tree_add`. -/
public
theorem treeAdd_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (ln: LeafNode Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: treeAdd t li ln = .success t')
  (ht: (TreeSync.mf tkt l).wf pred t) (hln: (LeafNode.mf tkt).wf pred ln):
  (TreeSync.mf tkt l).wf pred t'
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    obtain rfl := treeAdd_zero t li ln t' h
    simp [MlsOption.mf.wf_eq, hln]
  | node t ih =>
    obtain ⟨newContent, newChild, h1, rfl, -, -, hc⟩ := treeAdd_succ t li ln t' h
    have := Tree.mf.wf_child_sibling pred _ _ t li ht
    rw [Tree.mf.wf_succ] at ht
    simp only [Tree.mf.wf_pack_childSibling_node]
    refine ⟨?_, ih _ h1 this.1, this.2⟩
    cases hn: t.nodeContent <;> cases newContent <;> simp_all [MlsOption.mf.wf_eq, ParentNode.mf.wf_eq]

/-- Port of `pre_tree_hash`. -/
public
theorem pred_treeHash {l: Nat} (t: TreeSync Bytes tkt l) (th: Bytes)
  (h: treeHash t = .success th) (hcompat: PreIsHashCompatible pred) (hwf: (TreeSync.mf tkt l).wf pred t):
  pred th
:= by
  induction t using Tree.leftRightInduction generalizing th with
  | leaf t =>
    obtain ⟨hashInput, hinput, hhash⟩ := (treeHash_eq_success t th).mp h
    obtain ⟨-, rfl⟩ := (getTreeHashInput_zero t hashInput).mp hinput
    apply hcompat _ _ _ hhash
    rw [pred_serializeNE_iff (TreeHashInput.mf tkt) pred]
    grind [Tree.mf.wf_zero, TreeHashInput.mf.wf_eq, LeafNodeTreeHashInput.mf.wf_eq]
  | node t ihl ihr =>
    obtain ⟨hashInput, hinput, hhash⟩ := (treeHash_eq_success t th).mp h
    obtain ⟨leftHash, rightHash, hl, hr, rfl⟩ := (getTreeHashInput_succ t hashInput).mp hinput
    apply hcompat _ _ _ hhash
    rw [pred_serializeNE_iff (TreeHashInput.mf tkt) pred]
    grind [Tree.mf.wf_succ, TreeHashInput.mf.wf_eq, ParentNodeTreeHashInput.mf.wf_eq]

/-- Port of `pre_compute_parent_hash`. -/
public
theorem pred_computeParentHash {l: Nat}
  (content: tkt.NodeContent) (parentHash: Bytes) (originalSibling: TreeSync Bytes tkt l) (ph: Bytes)
  (h: computeParentHash content parentHash originalSibling = .success ph) (hcompat: PreIsHashCompatible pred)
  (hcontent: tkt.mfNodeContent.wf pred content) (hparentHash: pred parentHash)
  (hsibling: (TreeSync.mf tkt l).wf pred originalSibling):
  pred ph
:= by
  obtain ⟨hashInput, hinput, hhash⟩ := (computeParentHash_eq_success _ _ _ _).mp h
  obtain ⟨hc, hp, ht⟩ := (getParentHashInput_eq_success _ _ _ _).mp hinput
  apply hcompat _ _ _ hhash
  rw [pred_serializeNE_iff (ParentHashInput.mf tkt) pred, ParentHashInput.mf.wf_eq]
  have := pred_treeHash pred originalSibling _ ht hcompat hsibling
  grind

/-- Port of `is_well_formed_apply_path_aux`. -/
public
theorem applyPathAux_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (t': TreeSync Bytes tkt l)
  (h: applyPathAux t li p parentParentHash = .success t') (hcompat: PreIsHashCompatible pred)
  (ht: (TreeSync.mf tkt l).wf pred t) (hp: (PathSync.mf tkt l).wf pred p) (hpph: pred parentParentHash):
  (TreeSync.mf tkt l).wf pred t'
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t =>
    cases p with | leaf lp =>
    obtain rfl := applyPathAux_zero t li lp parentParentHash t' h
    rw [Path.mf.wf_leaf] at hp
    simp [MlsOption.mf.wf_eq, hp]
  | node t ih =>
    cases p with | node optExtContent pNext =>
    obtain ⟨newOptContent, newParentParentHash, newChild, hcn, h1, rfl⟩ :=
      applyPathAux_node t li optExtContent pNext parentParentHash t' h
    have hspec := computeNewNpAndPh_spec _ _ _ _ _ hcn
    have hcs := Tree.mf.wf_child_sibling pred _ _ t li ht
    rw [Path.mf.wf_node] at hp
    simp only [Tree.mf.wf_pack_childSibling_node]
    cases optExtContent with
    | none =>
      obtain ⟨rfl, rfl⟩ := hspec
      simp only [MlsOption.mf.wf_eq]
      grind
    | some extContent =>
      obtain ⟨content, rfl, hc, hph, -, hcph⟩ := hspec
      have hc' := hp.1
      simp only [MlsOption.mf.wf_eq] at hc'
      have := pred_computeParentHash pred _ _ _ _ hcph hcompat hc' hpph hcs.2
      simp only [MlsOption.mf.wf_eq, ParentNode.mf.wf_eq]
      exact ⟨⟨hc ▸ hc', hph ▸ hpph⟩, ih _ _ _ h1 hcs.1 hp.2 this, hcs.2⟩

/-- Port of `is_well_formed_apply_path`. -/
public
theorem applyPath_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (t': TreeSync Bytes tkt l)
  (h: applyPath t li p = .success t') (hcompat: PreIsHashCompatible pred)
  (ht: (TreeSync.mf tkt l).wf pred t) (hp: (PathSync.mf tkt l).wf pred p):
  (TreeSync.mf tkt l).wf pred t'
:=
  applyPathAux_wf pred t li p _ t' h hcompat ht hp
    (by simpa [rootParentHash] using BytesCompatiblePred.pred_empty (pred := pred))

/-- Port of `pre_compute_leaf_parent_hash_from_path`. -/
public
theorem pred_computeLeafParentHashFromPath {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (parentParentHash ph: Bytes)
  (h: computeLeafParentHashFromPath t li p parentParentHash = .success ph) (hcompat: PreIsHashCompatible pred)
  (ht: (TreeSync.mf tkt l).wf pred t) (hp: (ExternalPathSync.mf tkt l).wf pred p) (hpph: pred parentParentHash):
  pred ph
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t =>
    cases p
    rw [computeLeafParentHashFromPath_zero] at h
    grind
  | node t ih =>
    cases p with | node optExtContent pNext =>
    rw [computeLeafParentHashFromPath_node_eq, Result.bind_eq_success] at h
    obtain ⟨⟨newOptContent, newParentParentHash⟩, hcn, hnext⟩ := h
    have := computeNewNpAndPh_spec _ _ _ _ _ hcn
    have := Tree.mf.wf_child_sibling pred _ _ t li ht
    rw [Path.mf.wf_node] at hp
    apply ih _ _ hnext this.1 hp.2
    cases optExtContent <;> grind [pred_computeParentHash, MlsOption.mf.wf_eq]

/-- Port of `is_well_formed_get_path_leaf`. -/
public
theorem getPathLeaf_wf {l: Nat} (p: ExternalPathSync Bytes tkt l)
  (hp: (ExternalPathSync.mf tkt l).wf pred p):
  (LeafNodeData.mf tkt).wf pred p.getPathLeaf
:= by
  induction p <;> grind [Path.getPathLeaf, Path.mf.wf_leaf, Path.mf.wf_node]

/-- Port of `is_well_formed_set_path_leaf`. -/
public
theorem setPathLeaf_wf {l: Nat} (p: ExternalPathSync Bytes tkt l) (ln: LeafNode Bytes tkt)
  (hp: (ExternalPathSync.mf tkt l).wf pred p) (hln: (LeafNode.mf tkt).wf pred ln):
  (PathSync.mf tkt l).wf pred (p.setPathLeaf ln)
:= by
  induction p <;> grind [Path.setPathLeaf, Path.mf.wf_leaf, Path.mf.wf_node]

/-- Port of `is_well_formed_leaf_at`. -/
public
theorem leafAt_wf {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (ht: (TreeSync.mf tkt l).wf pred t):
  (MlsOption.mf (LeafNode.mf tkt)).wf pred (leafAt t li)
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    rw [Tree.mf.wf_zero] at ht
    grind [leafAt.eq_def]
  | node t ih =>
    have := Tree.mf.wf_child_sibling pred _ _ t li ht
    grind [leafAt.eq_def]

end CryptoBytes

section Symbolic

open DY

variable [HasSymbolicInvariants]

/-- Port of `pre_is_hash_compatible_is_publishable`. -/
public
theorem preIsHashCompatible_publishable (tr: ProofTrace):
  PreIsHashCompatible (Bytes.Publishable · tr)
:= by
  intro b h hb hh
  simp only [CryptoBytes.hashHash, Result.pure_eq_success] at hh
  grind [DY.Hash.hash.Invariant, DY.Hash.hash.label]

/-- Port of `pre_is_hash_compatible_is_knowable_by`. -/
public
theorem preIsHashCompatible_knowableBy (l: Label) (tr: ProofTrace):
  PreIsHashCompatible (Bytes.KnowableBy l · tr)
:= by
  intro b h hb hh
  simp only [CryptoBytes.hashHash, Result.pure_eq_success] at hh
  grind [DY.Hash.hash.Invariant, DY.Hash.hash.label]

/-- Port of `pre_is_hash_compatible_bytes_invariant`. -/
public
theorem preIsHashCompatible_invariant (tr: ProofTrace):
  PreIsHashCompatible (Bytes.Invariant · tr)
:= by
  intro b h hb hh
  simp only [CryptoBytes.hashHash, Result.pure_eq_success] at hh
  grind [DY.Hash.hash.Invariant]

end Symbolic

end MLS.TreeSync
