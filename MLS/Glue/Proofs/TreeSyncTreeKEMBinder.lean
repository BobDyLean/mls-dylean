module

public import MLS.Glue.Code.TreeSyncTreeKEMBinder
public import MLS.TreeSync.Proofs.API
public import MLS.TreeKEM.Proofs.API.Tree

/-!
Port of `MLS.TreeSyncTreeKEMBinder.Properties` and `MLS.TreeSyncTreeKEMBinder.Proofs`.

Port-specific differences:
- Both modules are in this file.
- The relations between paths are instances of `Path.Rel` (leaves and nodes related pointwise),
  so that the lemmas MLS* proves for each of them (e.g. `get_path_leaf_external_pathsync_pre_pathkem_rel`)
  follow from generic ones. `Path.Rel` relates paths of possibly different heights (it is then false):
  the heights of a TreeSync state and of a TreeKEM state are only propositionally equal.
- `treesync_treekem_state_rel` compares the trees as dependent pairs (with their heights).
  Proofs destruct related states with `treesyncTreekemStateRel_induction`.
- `*_path_secrets_rel` are existentials over the result of `pathSecretsToPrePathkem`, instead of a `match`.
- Lemmas about functions returning a `Result` take the result with a success hypothesis
  (MLS*'s `match … with | Success res -> … | _ -> True`).
- Lemmas about the TreeKEM state that need the refinements of `treekem_tree_state`
  (e.g. `fully_truncate_state_rel`) take `stTk.Valid` as an hypothesis.
- `is_well_formed_treesync_to_treekem` (about Comparse's `is_well_formed`, used by the symbolic proofs) is not ported.
-/

namespace MLS

open Comparse
open MLS.TreeSync MLS.TreeKEM

/-! ## Relations between paths -/

namespace Path

variable {Leaf1 Node1 Leaf2 Node2: Type}

/--
Two paths are related when their leaves are related by `RLeaf` and their nodes by `RNode`.
The paths may have different heights, in which case they are not related.
-/
@[expose]
public
def Rel (RLeaf: Leaf1 → Leaf2 → Prop) (RNode: Node1 → Node2 → Prop):
  {l1 l2: Nat} → Path Leaf1 Node1 l1 → Path Leaf2 Node2 l2 → Prop
  | _, _, .leaf a, .leaf b => RLeaf a b
  | _, _, .node a pa, .node b pb => Rel RLeaf RNode pa pb ∧ RNode a b
  | _, _, _, _ => False

/-- The leaves of related paths are related. -/
theorem Rel.getPathLeaf {RLeaf: Leaf1 → Leaf2 → Prop} {RNode: Node1 → Node2 → Prop} {l1 l2: Nat}
  {p1: Path Leaf1 Node1 l1} {p2: Path Leaf2 Node2 l2} (h: Rel RLeaf RNode p1 p2):
  RLeaf p1.getPathLeaf p2.getPathLeaf
:= by
  induction p1 generalizing l2 <;> cases p2 <;> simp_all [Rel, Path.getPathLeaf]

/-- Port of `get_path_leaf_set_path_leaf`. -/
@[simp]
public
theorem getPathLeaf_setPathLeaf {Leaf': Type} {l: Nat} (p: Path Leaf1 Node1 l) (x: Leaf'):
  (p.setPathLeaf x).getPathLeaf = x
:= by
  induction p <;> simp_all [Path.setPathLeaf, Path.getPathLeaf]

/-- Replacing the leaf of the first path by one related to the leaf of the second one. -/
theorem Rel.setPathLeaf {Leaf1': Type} {RLeaf: Leaf1 → Leaf2 → Prop} {RLeaf': Leaf1' → Leaf2 → Prop} {RNode: Node1 → Node2 → Prop}
  {l1 l2: Nat} {p1: Path Leaf1 Node1 l1} {p2: Path Leaf2 Node2 l2} (x: Leaf1')
  (h: Rel RLeaf RNode p1 p2) (hx: RLeaf' x p2.getPathLeaf):
  Rel RLeaf' RNode (p1.setPathLeaf x) p2
:= by
  induction p1 generalizing l2 <;> cases p2 <;> simp_all [Rel, Path.setPathLeaf, Path.getPathLeaf]

/-- A path is related to itself with its leaf replaced, when nodes are related to themselves. -/
theorem rel_setPathLeaf {Leaf1': Type} {RLeaf: Leaf1 → Leaf1' → Prop} {RNode: Node1 → Node1 → Prop}
  {l: Nat} (p: Path Leaf1 Node1 l) (x: Leaf1')
  (hnode: ∀ n, RNode n n) (hx: RLeaf p.getPathLeaf x):
  Rel RLeaf RNode p (p.setPathLeaf x)
:= by
  induction p <;> simp_all [Rel, Path.setPathLeaf, Path.getPathLeaf]

/-- If `p1` is related to `p2` and `p3`, then `p3` is related to `p2`. -/
theorem Rel.symm_trans {Leaf3 Node3: Type}
  {RLeaf12: Leaf1 → Leaf2 → Prop} {RNode12: Node1 → Node2 → Prop}
  {RLeaf13: Leaf1 → Leaf3 → Prop} {RNode13: Node1 → Node3 → Prop}
  {RLeaf32: Leaf3 → Leaf2 → Prop} {RNode32: Node3 → Node2 → Prop}
  {l1 l2 l3: Nat} {p1: Path Leaf1 Node1 l1} {p2: Path Leaf2 Node2 l2} {p3: Path Leaf3 Node3 l3}
  (h12: Rel RLeaf12 RNode12 p1 p2) (h13: Rel RLeaf13 RNode13 p1 p3)
  (hleaf: ∀ a b c, RLeaf12 a b → RLeaf13 a c → RLeaf32 c b) (hnode: ∀ a b c, RNode12 a b → RNode13 a c → RNode32 c b):
  Rel RLeaf32 RNode32 p3 p2
:= by
  induction p1 generalizing l2 l3 <;> cases p2 <;> cases p3 <;> simp_all [Rel] <;> grind

end Path

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-! ## Relations (`MLS.TreeSyncTreeKEMBinder.Properties`) -/

/-- Port of `treesync_treekem_rel`. -/
@[expose]
public
def treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l): Prop :=
  treesyncToTreekem ts = tk

/--
Port of `treesync_treekem_state_rel`.
The trees have the same height (MLS*'s `st_ts.levels == st_tk.levels`): they are compared as dependent pairs.
-/
@[expose]
public
def treesyncTreekemStateRel {TokenT: Type} {groupId: MlsBytes Bytes} {leafInd: Nat}
  (stTs: TreeSyncState Bytes tkt TokenT groupId) (stTk: TreeKEMTreeState Bytes leafInd): Prop
:=
  (⟨stTs.levels, treesyncToTreekem stTs.tree⟩: (l: Nat) × TreeKEM Bytes l) = ⟨stTk.levels, stTk.tree⟩

/-- Port of `external_pathsync_pre_pathkem_rel`. -/
@[expose]
public
def externalPathsyncPrePathkemRel {l1 l2: Nat} (ps: ExternalPathSync Bytes tkt l1) (pk: PrePathKEM Bytes l2): Prop :=
  Path.Rel (fun lns lnk => lns.content.val = lnk.publicKey) (fun opns opnk => opns = opnk) ps pk

/-- Port of `external_pathsync_pathsync_rel`. -/
@[expose]
public
def externalPathsyncPathsyncRel {tkt: TreeKEMTypes Bytes} {l1 l2: Nat}
  (eps: ExternalPathSync Bytes tkt l1) (ps: PathSync Bytes tkt l2): Prop
:=
  Path.Rel (fun eln ln => eln.content = ln.data.content) (fun opns opnk => opns = opnk) eps ps

/-- Port of `pathsync_pre_pathkem_rel`. -/
@[expose]
public
def pathsyncPrePathkemRel {l1 l2: Nat} (ps: PathSync Bytes tkt l1) (pk: PrePathKEM Bytes l2): Prop :=
  Path.Rel (fun lns lnk => lns.data.content.val = lnk.publicKey) (fun opns opnk => opns = opnk) ps pk

/-- Port of `pathsync_pathkem_rel`. -/
@[expose]
public
def pathsyncPathkemRel {l1 l2: Nat} (ps: PathSync Bytes tkt l1) (pk: PathKEM Bytes l2): Prop :=
  Path.Rel (fun lns lnk => lns.data.content.val = lnk.publicKey)
    (fun opns opnk =>
      match opns, opnk with
      | some pns, some pnk => pns = pnk.encryptionKey
      | none, none => True
      | _, _ => False)
    ps pk

/-- Port of `external_pathsync_path_secrets_rel`. -/
@[expose]
public
def externalPathsyncPathSecretsRel {l1 l2: Nat} (psync: ExternalPathSync Bytes tkt l1) (psecrets: PathSecrets Bytes l2): Prop :=
  ∃ ppk, pathSecretsToPrePathkem psecrets = .success ppk ∧ externalPathsyncPrePathkemRel psync ppk

/-- Port of `pathsync_path_secrets_rel`. -/
@[expose]
public
def pathsyncPathSecretsRel {l1 l2: Nat} (psync: PathSync Bytes tkt l1) (psecrets: PathSecrets Bytes l2): Prop :=
  ∃ ppk, pathSecretsToPrePathkem psecrets = .success ppk ∧ pathsyncPrePathkemRel psync ppk

/-! ## Unfolding `treesyncToTreekem` -/

/-- The TreeKEM leaf of a TreeSync leaf. -/
public
abbrev leafNodeToTreekemLeaf (ln: LeafNode Bytes tkt): TreeKEMLeaf Bytes :=
  { publicKey := ln.data.content.val }

@[simp]
theorem leafNodeToTreekemLeaf_eq_iff (ln: LeafNode Bytes tkt) (lnK: TreeKEMLeaf Bytes):
  leafNodeToTreekemLeaf ln = lnK ↔ ln.data.content.val = lnK.publicKey
:= by
  cases lnK
  simp

/-- `treesyncToTreekem` on a leaf. -/
public
theorem treesyncToTreekem_zero (t: TreeSync Bytes tkt 0):
  treesyncToTreekem t = (LeftRightView.leaf (t.leafContent.map leafNodeToTreekemLeaf) t.position).pack
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  rw [treesyncToTreekem.eq_def]
  cases c <;> rfl

/-- `treesyncToTreekem` on a node. -/
public
theorem treesyncToTreekem_left_right {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  treesyncToTreekem t =
    (LeftRightView.node (t.nodeContent.map treesyncToTreekemNode) (treesyncToTreekem t.left) (treesyncToTreekem t.right)).pack
:= by
  obtain ⟨_, ⟨⟩⟩ := t
  rw [treesyncToTreekem.eq_def]
  rfl

@[simp]
public
theorem treesyncToTreekem_position {l: Nat} (t: TreeSync Bytes tkt l):
  (treesyncToTreekem t).position = t.position
:= by
  induction t using Tree.leftRightInduction <;> simp_all [treesyncToTreekem_zero, treesyncToTreekem_left_right]

grind_pattern treesyncToTreekem_position => (treesyncToTreekem t).position

@[simp]
public
theorem leafContent_treesyncToTreekem (t: TreeSync Bytes tkt 0):
  (treesyncToTreekem t).leafContent = t.leafContent.map leafNodeToTreekemLeaf
:= by
  simp [treesyncToTreekem_zero]

@[simp]
public
theorem nodeContent_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  (treesyncToTreekem t).nodeContent = t.nodeContent.map treesyncToTreekemNode
:= by
  simp [treesyncToTreekem_left_right]

@[simp]
public
theorem left_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  (treesyncToTreekem t).left = treesyncToTreekem t.left
:= by
  simp [treesyncToTreekem_left_right]

@[simp]
public
theorem right_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  (treesyncToTreekem t).right = treesyncToTreekem t.right
:= by
  simp [treesyncToTreekem_left_right]

@[simp]
public
theorem child_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  (treesyncToTreekem t).child li = treesyncToTreekem (t.child li)
:= by
  grind [treesyncToTreekem_left_right]

@[simp]
public
theorem sibling_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  (treesyncToTreekem t).sibling li = treesyncToTreekem (t.sibling li)
:= by
  grind [treesyncToTreekem_left_right]

/-! ## Paths and trees -/

/-- Port of `is_tree_empty_treesync_to_treekem`. -/
public
theorem isTreeEmpty_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt l):
  isTreeEmpty (treesyncToTreekem t) = isTreeEmpty t
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => simp [isTreeEmpty_zero]
  | node t ihl ihr =>
    rw [isTreeEmpty_succ _ t.position, isTreeEmpty_succ _ t.position]
    simp [Tree.child_position, Tree.sibling_position, ihl, ihr]

/-- Port of `treesync_treekem_rel_is_tree_empty`. -/
public
theorem treesyncTreekemRel_isTreeEmpty {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l)
  (hrel: treesyncTreekemRel ts tk):
  isTreeEmpty ts = isTreeEmpty tk
:= by
  rw [← hrel, isTreeEmpty_treesyncToTreekem]

/-- Port of `path_filtering_ok_treesync_to_treekem`. -/
public
theorem pathFilteringOk_treesyncToTreekem {l: Nat} {PathLeaf PathNode: Type}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: Path PathLeaf (Option PathNode) l):
  pathFilteringOk (treesyncToTreekem t) li p = pathFilteringOk t li p
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih => cases p; simp [ih, isTreeEmpty_treesyncToTreekem]

/-- Port of `get_path_leaf_external_pathsync_pre_pathkem_rel`. -/
public
theorem getPathLeaf_externalPathsyncPrePathkemRel {l: Nat} (ps: ExternalPathSync Bytes tkt l) (pk: PrePathKEM Bytes l)
  (h: externalPathsyncPrePathkemRel ps pk):
  ps.getPathLeaf.content.val = pk.getPathLeaf.publicKey
:=
  Path.Rel.getPathLeaf h

/-- Port of `get_path_leaf_pathsync_pre_pathkem_rel`. -/
public
theorem getPathLeaf_pathsyncPrePathkemRel {l: Nat} (ps: PathSync Bytes tkt l) (pk: PrePathKEM Bytes l)
  (h: pathsyncPrePathkemRel ps pk):
  ps.getPathLeaf.data.content.val = pk.getPathLeaf.publicKey
:=
  Path.Rel.getPathLeaf h

/-- Port of `pathsync_pathkem_rel_update_path_to_treeX`. -/
public
theorem pathsyncPathkemRel_updatePathToTreeX {l: Nat} (p: SparseUpdatePath Bytes l):
  pathsyncPathkemRel (updatePathToTreesync p) (updatePathToTreekem p)
:= by
  suffices ∀ (lnK: TreeKEMLeaf Bytes), p.getPathLeaf.data.content.val = lnK.publicKey →
      pathsyncPathkemRel (updatePathToTreesync p) (p.setPathLeaf lnK) from
    this _ rfl
  induction p with
  | leaf ln => simp [pathsyncPathkemRel, Path.Rel, updatePathToTreesync, Path.setPathLeaf, Path.getPathLeaf]
  | node onp pNext ih =>
    intro lnK h
    cases onp <;> simp_all [pathsyncPathkemRel, Path.Rel, updatePathToTreesync, Path.setPathLeaf, Path.getPathLeaf] <;> trivial

/-- Port of `treekem_to_treesync_lemmas`. -/
public
theorem treekemToTreesync_lemmas {l: Nat} (lnData: LeafNodeData Bytes tkt) (p: PrePathKEM Bytes l)
  (res: ExternalPathSync Bytes tkt l) (h: treekemToTreesync lnData p = .success res):
  (∃ content: MlsBytes Bytes, content.val = p.getPathLeaf.publicKey ∧ res.getPathLeaf = { lnData with content }) ∧
  externalPathsyncPrePathkemRel res p
:= by
  induction p with
  | leaf mi =>
    simp only [treekemToTreesync, Result.bind_eq_success, Result.pure_eq_success, mkMlsBytes_eq_success] at h
    obtain ⟨content, hc, rfl⟩ := h
    exact ⟨⟨content, hc.symm, rfl⟩, hc.symm⟩
  | node okp pNext ih =>
    simp only [treekemToTreesync, Result.bind_eq_success, Result.pure_eq_success] at h
    obtain ⟨next, h1, rfl⟩ := h
    obtain ⟨hleaf, hrel⟩ := ih next h1
    exact ⟨hleaf, hrel, rfl⟩

/-! ## `treesync_treekem_rel` preservation lemmas -/

/-- Port of `tree_create_treesync_treekem_rel`. -/
theorem treeCreate_treesyncTreekemRel (lnS: LeafNode Bytes tkt) (lnK: TreeKEMLeaf Bytes)
  (hln: lnS.data.content.val = lnK.publicKey):
  treesyncTreekemRel (treeCreate lnS) (treeCreate lnK)
:= by
  apply Tree.ext_zero <;> simp [treeCreate, hln]

/-- Port of `tree_add_treesync_treekem_rel_aux`. -/
theorem map_toNat_insertSorted (x: UInt32) (l: List UInt32):
  (insertSorted x l).map UInt32.toNat = insertSorted x.toNat (l.map UInt32.toNat)
:= by
  induction l <;> grind [insertSorted]

/-- Port of `tree_add_treesync_treekem_rel`. -/
theorem treeAdd_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (li: Nat) (lnS: LeafNode Bytes tkt)
  (tk: TreeKEM Bytes l) (lnK: TreeKEMLeaf Bytes) (resS: TreeSync Bytes tkt l) (h: TreeSync.treeAdd ts li lnS = .success resS)
  (hrel: treesyncTreekemRel ts tk) (hln: lnS.data.content.val = lnK.publicKey):
  treesyncTreekemRel resS (treeAdd tk li lnK)
:= by
  unfold treesyncTreekemRel at *
  subst hrel
  induction ts using Tree.childInduction li with
  | leaf ts =>
    rw [TreeSync.treeAdd_zero ts li lnS resS h, TreeKEM.treeAdd_zero]
    apply Tree.ext_zero <;> simp [hln]
  | node ts ih =>
    obtain ⟨newContent, newChild, h1, rfl, hul, hli, hc⟩ := TreeSync.treeAdd_succ ts li lnS resS h
    apply Tree.ext_succ li <;> simp [ih _ h1, TreeSync.treeAdd_position _ _ _ _ h1]
    cases hts: ts.nodeContent <;> cases newContent <;> simp_all [treesyncToTreekemNode, map_toNat_insertSorted, Nat.mod_eq_of_lt]

/-- `treesyncToTreekem` commutes with `treeChangePath` when blanking the nodes (as `treeUpdate` and `treeRemove` do). -/
theorem treesyncToTreekem_treeChangePath {l: Nat} (ts: TreeSync Bytes tkt l) (li: Nat) (oln: Option (LeafNode Bytes tkt)):
  treesyncToTreekem (treeChangePath ts li oln none) = treeChangePath (treesyncToTreekem ts) li (oln.map leafNodeToTreekemLeaf) none
:= by
  induction ts using Tree.childInduction li with
  | leaf ts => apply Tree.ext_zero <;> unfold treeChangePath <;> simp
  | node ts ih => apply Tree.ext_succ li <;> simp [ih]

/-- Port of `tree_update_treesync_treekem_rel`. -/
theorem treeUpdate_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l)
  (lnS: LeafNode Bytes tkt) (lnK: TreeKEMLeaf Bytes) (li: Nat)
  (hln: lnS.data.content.val = lnK.publicKey) (hrel: treesyncTreekemRel ts tk):
  treesyncTreekemRel (treeUpdate ts li lnS) (treeUpdate tk li lnK)
:= by
  unfold treesyncTreekemRel at *
  subst hrel
  have: leafNodeToTreekemLeaf lnS = lnK := by simp [hln]
  simp [treeUpdate, treesyncToTreekem_treeChangePath, this]

/-- Port of `tree_remove_treesync_treekem_rel`. -/
theorem treeRemove_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l) (li: Nat)
  (hrel: treesyncTreekemRel ts tk):
  treesyncTreekemRel (treeRemove ts li) (treeRemove tk li)
:= by
  unfold treesyncTreekemRel at *
  subst hrel
  simp [treeRemove, treesyncToTreekem_treeChangePath]

/-- Port of `apply_path_aux_treesync_treekem_rel`. -/
theorem applyPathAux_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l) (li: Nat)
  (ps: PathSync Bytes tkt l) (pk: PathKEM Bytes l) (parentParentHash: Bytes)
  (resS: TreeSync Bytes tkt l) (h: applyPathAux ts li ps parentParentHash = .success resS)
  (hrel: treesyncTreekemRel ts tk) (hp: pathsyncPathkemRel ps pk):
  treesyncTreekemRel resS (treeApplyPath tk li pk)
:= by
  unfold treesyncTreekemRel pathsyncPathkemRel at *
  subst hrel
  induction ts using Tree.childInduction li generalizing parentParentHash with
  | leaf ts =>
    cases ps
    cases pk
    rw [applyPathAux_zero ts li _ parentParentHash resS h, treeApplyPath_zero]
    apply Tree.ext_zero <;> simp_all [Path.Rel, Path.getPathLeaf]
  | node ts ih =>
    cases ps with | node optExtContent psNext =>
    cases pk with | node oupn pkNext =>
    obtain ⟨hpNext, hpNode⟩ := hp
    obtain ⟨newOptContent, newParentParentHash, newChild, h1, h2, rfl⟩ := applyPathAux_node ts li _ _ _ resS h
    have ih := ih _ _ _ _ h2 hpNext
    have := applyPathAux_position _ _ _ _ _ h2
    have := computeNewNpAndPh_spec _ _ _ _ _ h1
    cases optExtContent <;> cases oupn <;> simp at hpNode
    · apply Tree.ext_succ li <;> simp_all
    · apply Tree.ext_succ li <;> simp_all [treesyncToTreekemNode] <;> grind

/-- Port of `apply_path_treesync_treekem_rel`. -/
public
theorem applyPath_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l) (li: Nat)
  (ps: PathSync Bytes tkt l) (pk: PathKEM Bytes l)
  (resS: TreeSync Bytes tkt l) (h: applyPath ts li ps = .success resS)
  (hrel: treesyncTreekemRel ts tk) (hp: pathsyncPathkemRel ps pk):
  treesyncTreekemRel resS (treeApplyPath tk li pk)
:=
  applyPathAux_treesyncTreekemRel ts tk li ps pk _ resS h hrel hp

/-- Port of `mk_blank_tree_treesync_treekem_rel`. -/
theorem mkBlankTree_treesyncTreekemRel (l p: Nat):
  treesyncTreekemRel (mkBlankTree l p: TreeSync Bytes tkt l) (mkBlankTree l p)
:= by
  unfold treesyncTreekemRel
  induction l generalizing p with
  | zero => apply Tree.ext_zero <;> simp [mkBlankTree, mkBlankTreeGeneral]
  | succ l ih => simp_all [mkBlankTree, mkBlankTreeGeneral, treesyncToTreekem_left_right]

/-- Port of `tree_extend_treesync_treekem_rel`. -/
theorem treeExtend_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l)
  (hrel: treesyncTreekemRel ts tk):
  treesyncTreekemRel (treeExtend ts) (treeExtend tk)
:= by
  subst hrel
  have := mkBlankTree_treesyncTreekemRel (Bytes := Bytes) l (ts.position + 2^l)
  simp_all [treeExtend, treesyncTreekemRel, treesyncToTreekem_left_right, mkBlankTree]

/-- The data of the leaf computed by `externalPathToPathAux`. -/
theorem externalPathToPathAux_data {tkt: TreeKEMTypes Bytes} {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (signKey nonce: Bytes) (ln: LeafNode Bytes tkt)
  (h: externalPathToPathAux t li p groupId signKey nonce = .success ln):
  ∃ parentHash, ln.data = { p.getPathLeaf with source := .commit, lifetime := (), parentHash }
:= by
  simp only [externalPathToPathAux, Result.bind_eq_success, Result.pure_eq_success] at h
  grind

/-- Port of `pathsync_pre_pathkem_rel_external_path_to_path_aux`. -/
public
theorem pathsyncPrePathkemRel_externalPathToPathAux {l: Nat} (ln: LeafNode Bytes tkt) (ps: ExternalPathSync Bytes tkt l)
  (pk: PrePathKEM Bytes l)
  (_hsource: ps.getPathLeaf.source = .update) (hln: ln.data.content.val = pk.getPathLeaf.publicKey)
  (hrel: externalPathsyncPrePathkemRel ps pk):
  pathsyncPrePathkemRel (ps.setPathLeaf ln) pk
:=
  Path.Rel.setPathLeaf ln hrel hln

/-- Port of `pathsync_pre_pathkem_rel_external_path_to_path`. -/
public
theorem pathsyncPrePathkemRel_externalPathToPath {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (ps: ExternalPathSync Bytes tkt l) (pk: PrePathKEM Bytes l) (groupId: MlsBytes Bytes) (signKey signNonce: Bytes)
  (res: PathSync Bytes tkt l) (h: externalPathToPath t li ps groupId signKey signNonce = .success res)
  (hsource: ps.getPathLeaf.source = .update) (hrel: externalPathsyncPrePathkemRel ps pk):
  pathsyncPrePathkemRel res pk
:= by
  simp only [externalPathToPath, Result.bind_eq_success, Result.pure_eq_success] at h
  obtain ⟨ln, h1, rfl⟩ := h
  obtain ⟨parentHash, hln⟩ := externalPathToPathAux_data _ _ _ _ _ _ _ h1
  apply pathsyncPrePathkemRel_externalPathToPathAux ln ps pk hsource _ hrel
  rw [hln, ← getPathLeaf_externalPathsyncPrePathkemRel ps pk hrel]

/-- Port of `leaf_at_treesync_to_treekem`, stated as an equation. -/
public
theorem leafAt_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat):
  leafAt (treesyncToTreekem t) li = (leafAt t li).map leafNodeToTreekemLeaf
:= by
  induction t using Tree.childInduction li with
  | leaf t => rw [leafAt.eq_def, leafAt.eq_def]; simp
  | node t ih => rw [leafAt.eq_def, leafAt.eq_def]; simp [ih]

/-- Port of `treesync_to_treekem_invariant`. -/
theorem treesyncToTreekem_invariant {l: Nat} (t: TreeSync Bytes tkt l) (h: unmergedLeavesOk t):
  treekemInvariant (treesyncToTreekem t)
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => exact treekemInvariant_zero _
  | node t ihl ihr =>
    rw [unmergedLeavesOk_succ _ t.position] at h
    rw [treekemInvariant_left_right]
    cases hc: t.nodeContent <;>
      simp_all [Tree.child_position, Tree.sibling_position, treesyncToTreekemNode, TreeKEM.unmergedLeafExists,
        TreeSync.unmergedLeafExists, leafAt_treesyncToTreekem, Tree.containsLeafIndex]

/-! ## `treesync_treekem_state_rel` preservation lemmas -/

section State

variable {TokenT: Type} {groupId: MlsBytes Bytes} {leafInd: Nat}

/-- States with the same height and related trees are related. -/
public
theorem treesyncTreekemStateRel_mk {l: Nat} (tsTree: TreeSync Bytes tkt l) (tokens: ASTokens TokenT l)
  (tkTree: TreeKEM Bytes l) (priv: TreeKEMPriv Bytes l) (h: treesyncTreekemRel tsTree tkTree):
  treesyncTreekemStateRel
    ({ levels := l, tree := tsTree, tokens }: TreeSyncState Bytes tkt TokenT groupId)
    ({ levels := l, tree := tkTree, priv }: TreeKEMTreeState Bytes leafInd)
:= by
  unfold treesyncTreekemRel at h
  simp [treesyncTreekemStateRel, h]

/-- Induction on related states: they have the same height, and their trees are related. -/
@[elab_as_elim]
public
theorem treesyncTreekemStateRel_induction
  {motive: (stTs: TreeSyncState Bytes tkt TokenT groupId) → (stTk: TreeKEMTreeState Bytes leafInd) →
    treesyncTreekemStateRel stTs stTk → Prop}
  (mk: ∀ (l: Nat) (tsTree: TreeSync Bytes tkt l) (tokens: ASTokens TokenT l) (priv: TreeKEMPriv Bytes l),
    motive { levels := l, tree := tsTree, tokens } { levels := l, tree := treesyncToTreekem tsTree, priv }
      (treesyncTreekemStateRel_mk _ _ _ _ rfl))
  (stTs: TreeSyncState Bytes tkt TokenT groupId) (stTk: TreeKEMTreeState Bytes leafInd)
  (hrel: treesyncTreekemStateRel stTs stTk):
  motive stTs stTk hrel
:= by
  obtain ⟨l, tsTree, tokens⟩ := stTs
  obtain ⟨l', tkTree, priv⟩ := stTk
  obtain ⟨rfl, hrel'⟩ := Sigma.mk.inj hrel
  subst hrel'
  exact mk l tsTree tokens priv

/-- Port of `create_state_rel`. -/
public
theorem create_stateRel {ln: LeafNode Bytes tkt} (pend: TreeSync.API.PendingCreate groupId ln) (token: TokenT)
  (leafPrivateKey leafPublicKey: Bytes) (hln: ln.data.content.val = leafPublicKey):
  treesyncTreekemStateRel (TreeSync.API.finalizeCreate pend token) (TreeKEM.API.Tree.create leafPrivateKey leafPublicKey)
:=
  treesyncTreekemStateRel_mk _ _ _ _ (treeCreate_treesyncTreekemRel ln _ hln)

/-- Port of `welcome_state_rel`. -/
public
theorem welcome_stateRel {l: Nat} {ts: TreeSync Bytes tkt l} (pend: TreeSync.API.PendingWelcome groupId ts)
  (tokens: List (Option TokenT)) (tk: TreeKEM Bytes l) (leafDecryptionKey: Bytes)
  (optPathSecretAndInviterInd: Option (Bytes × Nat)) (leafInd: Nat)
  (hpend: pend.Valid) (_hli: tk.containsLeafIndex leafInd) (_hleaf: (leafAt tk leafInd).isSome)
  (hrel: treesyncTreekemRel ts tk):
  treekemInvariant tk ∧
  ∀ res, TreeKEM.API.Tree.welcome tk leafDecryptionKey optPathSecretAndInviterInd leafInd = .success res →
    treesyncTreekemStateRel (TreeSync.API.finalizeWelcome pend tokens) res
:= by
  refine ⟨hrel ▸ treesyncToTreekem_invariant ts hpend.1.1, fun res h => ?_⟩
  obtain ⟨priv, rfl⟩ := TreeKEM.API.Tree.welcome_success _ _ _ _ _ h
  exact treesyncTreekemStateRel_mk _ _ _ _ hrel

/-- `findEmptyLeaf` only depends on the blank leaves, which `treesyncToTreekem` preserves. -/
theorem findEmptyLeaf_treesyncToTreekem {l: Nat} (t: TreeSync Bytes tkt l):
  findEmptyLeaf (treesyncToTreekem t) = findEmptyLeaf t
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => unfold findEmptyLeaf; simp
  | node t ihl ihr => unfold findEmptyLeaf; simp [ihl, ihr]

/-- Port of `find_empty_leaf_treesync_treekem_rel`, stated as an equation. -/
public
theorem findEmptyLeaf_treesyncTreekemRel {l: Nat} (ts: TreeSync Bytes tkt l) (tk: TreeKEM Bytes l)
  (hrel: treesyncTreekemRel ts tk):
  findEmptyLeaf ts = findEmptyLeaf tk
:= by
  rw [← hrel, findEmptyLeaf_treesyncToTreekem]

/-- Port of `add_state_rel`. -/
public
theorem add_stateRel {st: TreeSyncState Bytes tkt TokenT groupId} {lnS: LeafNode Bytes tkt}
  (pend: TreeSync.API.PendingAdd st lnS) (token: TokenT) (stTk: TreeKEMTreeState Bytes leafInd) (lnK: TreeKEMLeaf Bytes)
  (res: TreeSyncState Bytes tkt TokenT groupId) (li: Nat) (h: TreeSync.API.finalizeAdd pend token = .success (res, li))
  (hrel: treesyncTreekemStateRel st stTk) (hln: lnS.data.content.val = lnK.publicKey):
  treesyncTreekemStateRel res (TreeKEM.API.Tree.add stTk lnK).1 ∧ li = (TreeKEM.API.Tree.add stTk lnK).2
:= by
  induction st, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  rcases TreeSync.API.finalizeAdd_success pend token res li h with ⟨heq, newTree, h1, rfl⟩ | ⟨heq, heq', newTree, h1, rfl⟩
  · simp only [TreeKEM.API.Tree.add, findEmptyLeaf_treesyncToTreekem, heq]
    exact ⟨treesyncTreekemStateRel_mk _ _ _ _ (treeAdd_treesyncTreekemRel _ _ _ _ _ _ h1 rfl hln), trivial⟩
  · have hext := treeExtend_treesyncTreekemRel tsTree _ rfl
    unfold treesyncTreekemRel at hext
    simp only [TreeKEM.API.Tree.add, findEmptyLeaf_treesyncToTreekem, heq, ← hext, heq', Option.getD_some]
    exact ⟨treesyncTreekemStateRel_mk _ _ _ _ (treeAdd_treesyncTreekemRel _ _ _ _ _ _ h1 rfl hln), trivial⟩

/-- Port of `update_myself_state_rel`. -/
public
theorem updateMyself_stateRel {st: TreeSyncState Bytes tkt TokenT groupId} {lnS: LeafNode Bytes tkt} {li: Nat}
  (pend: TreeSync.API.PendingUpdate st lnS li) (token: TokenT)
  (stTk: TreeKEMTreeState Bytes leafInd) (lnK: TreeKEMLeaf Bytes) (leafDecryptionKey: Bytes)
  (hli: leafInd = li) (hrel: treesyncTreekemStateRel st stTk) (hln: lnS.data.content.val = lnK.publicKey):
  treesyncTreekemStateRel (TreeSync.API.finalizeUpdate pend token) (TreeKEM.API.Tree.updateMyself stTk lnK leafDecryptionKey)
:= by
  induction st, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  subst hli
  exact treesyncTreekemStateRel_mk _ _ _ _ (treeUpdate_treesyncTreekemRel _ _ _ _ _ hln rfl)

/--
Port of `update_other_state_rel`.
MLS* requires `i < pow2 st_tk.levels` (here `_hi`) and `i <> leaf_ind`.
-/
public
theorem updateOther_stateRel {st: TreeSyncState Bytes tkt TokenT groupId} {lnS: LeafNode Bytes tkt} {li: Nat}
  (pend: TreeSync.API.PendingUpdate st lnS li) (token: TokenT)
  (stTk: TreeKEMTreeState Bytes leafInd) (lnK: TreeKEMLeaf Bytes) (i: Nat)
  (_hi: stTk.tree.containsLeafIndex i) (_hne: i ≠ leafInd)
  (hli: i = li) (hrel: treesyncTreekemStateRel st stTk) (hln: lnS.data.content.val = lnK.publicKey):
  treesyncTreekemStateRel (TreeSync.API.finalizeUpdate pend token) (TreeKEM.API.Tree.updateOther stTk lnK i)
:= by
  induction st, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  subst hli
  exact treesyncTreekemStateRel_mk _ _ _ _ (treeUpdate_treesyncTreekemRel _ _ _ _ _ hln rfl)

/--
Port of `fully_truncate_state_rel`.
MLS* requires the refinements of `st_tk` (here `hst`), from which the leaf index is in the left subtree when truncating.
-/
public
theorem fullyTruncate_stateRel (stTs: TreeSyncState Bytes tkt TokenT groupId) (stTk: TreeKEMTreeState Bytes leafInd)
  (hrel: treesyncTreekemStateRel stTs stTk) (hst: stTk.Valid):
  treesyncTreekemStateRel (TreeSync.API.fullyTruncateState stTs) (TreeKEM.API.Tree.fullyTruncate stTk)
:= by
  induction stTs, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  induction l with
  | zero =>
    have htrunc: TreeKEM.API.Tree.truncateOne ({ levels := 0, tree := treesyncToTreekem tsTree, priv }: TreeKEMTreeState Bytes leafInd) = none := by
      simp [TreeKEM.API.Tree.truncateOne]
    rw [TreeKEM.API.Tree.fullyTruncate, htrunc]
    simp only [TreeSync.API.fullyTruncateState]
    exact treesyncTreekemStateRel_mk _ _ _ _ rfl
  | succ l ih =>
    rw [TreeSync.API.fullyTruncateState, TreeKEM.API.Tree.fullyTruncate]
    by_cases hempty: isTreeEmpty tsTree.right
    · have hli: leafInd < 2^l := by
        obtain ⟨hpos, -, hc, hleaf⟩ := hst
        have := leafAt_of_isTreeEmpty (treesyncToTreekem tsTree).right leafInd (by simp [isTreeEmpty_treesyncToTreekem, hempty])
        grind [leafAt.eq_def]
      have htrunc: TreeKEM.API.Tree.truncateOne ({ levels := l+1, tree := treesyncToTreekem tsTree, priv }: TreeKEMTreeState Bytes leafInd) =
          some ⟨{ levels := l, tree := treeTruncate (treesyncToTreekem tsTree), priv := pathTruncate priv }, rfl⟩ := by
        simp [TreeKEM.API.Tree.truncateOne, isTreeEmpty_treesyncToTreekem, hempty, hli]
      simp only [hempty, htrunc]
      have hvalid := TreeKEM.API.Tree.truncateOne_valid _ _ htrunc hst
      simp only [treeTruncate, left_treesyncToTreekem] at hvalid ⊢
      exact ih _ _ _ hvalid
    · have htrunc: TreeKEM.API.Tree.truncateOne ({ levels := l+1, tree := treesyncToTreekem tsTree, priv }: TreeKEMTreeState Bytes leafInd) = none := by
        simp [TreeKEM.API.Tree.truncateOne, isTreeEmpty_treesyncToTreekem, hempty]
      simp only [hempty, htrunc]
      exact treesyncTreekemStateRel_mk _ _ _ _ rfl

/--
Port of `remove_state_rel`.
MLS* requires `i < pow2 st_tk.levels` (here `hi`), `i <> leaf_ind`, and the refinements of `st_tk` (here `hst`).
-/
public
theorem remove_stateRel {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat}
  (pend: TreeSync.API.PendingRemove st li) (stTk: TreeKEMTreeState Bytes leafInd) (i: Nat)
  (hi: stTk.tree.containsLeafIndex i) (hne: i ≠ leafInd)
  (hli: li = i) (hrel: treesyncTreekemStateRel st stTk) (hst: stTk.Valid):
  treesyncTreekemStateRel (TreeSync.API.finalizeRemove pend) (TreeKEM.API.Tree.remove stTk i)
:= by
  apply fullyTruncate_stateRel _ _ _ (TreeKEM.API.Tree.removeAux_valid stTk i hi hne hst)
  induction st, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  subst hli
  exact treesyncTreekemStateRel_mk _ _ _ _ (treeRemove_treesyncTreekemRel _ _ _ rfl)

/-- Port of `process_commit_state_rel`. -/
public
theorem processCommit_stateRel {st: TreeSyncState Bytes tkt TokenT groupId} {liTs: Nat} {pTs: PathSync Bytes tkt st.levels}
  (pend: TreeSync.API.PendingCommit st liTs pTs) (token: TokenT)
  (stTk: TreeKEMTreeState Bytes leafInd) (liTk: Nat) (pTk: PathKEM Bytes stTk.levels) (excludedLeaves: List Nat)
  (groupContext: GroupContext Bytes)
  (resTs: TreeSyncState Bytes tkt TokenT groupId) (resTk: TreeKEMTreeState Bytes leafInd) (commitSecret: Bytes)
  (hTs: TreeSync.API.finalizeCommit pend token = .success resTs)
  (hTk: TreeKEM.API.Tree.commit stTk liTk pTk excludedLeaves groupContext = .success (resTk, commitSecret))
  (_hliTk: stTk.tree.containsLeafIndex liTk) (_hne: liTk ≠ leafInd) (_hfilter: pathFilteringOk stTk.tree liTk pTk)
  (_hexcluded: leafInd ∉ excludedLeaves)
  (hli: liTs = liTk) (hrel: treesyncTreekemStateRel st stTk) (hp: pathsyncPathkemRel pTs pTk):
  treesyncTreekemStateRel resTs resTk
:= by
  obtain ⟨newTree, h1, rfl⟩ := TreeSync.API.finalizeCommit_success pend token resTs hTs
  obtain ⟨newPriv, rfl⟩ := TreeKEM.API.Tree.commit_success stTk liTk pTk excludedLeaves groupContext resTk commitSecret hTk
  induction st, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  subst hli
  exact treesyncTreekemStateRel_mk _ _ _ _ (applyPath_treesyncTreekemRel _ _ _ _ _ _ h1 rfl hp)

/-- The leaf of `pathSecretsToPrePathkem p` is the public key generated from the leaf of `p`. -/
public
theorem pathSecretsToPrePathkem_getPathLeaf {l: Nat} (p: PathSecrets Bytes l) (ppk: PrePathKEM Bytes l)
  (h: pathSecretsToPrePathkem p = .success ppk):
  ∃ sk, CryptoBytes.hpkeGenKeypair p.getPathLeaf = .success (sk, ppk.getPathLeaf.publicKey)
:= by
  induction p with
  | leaf leafSk =>
    simp only [pathSecretsToPrePathkem, Result.bind_eq_success, Result.pure_eq_success] at h
    grind [Path.getPathLeaf]
  | node opn pNext ih =>
    cases opn <;> simp only [pathSecretsToPrePathkem, Result.bind_eq_success, Result.pure_eq_success] at h <;>
      grind [Path.getPathLeaf]

/-- One step of `pathSecretsToPrePathkem` on a node. -/
public
theorem pathSecretsToPrePathkem_node {l: Nat} (opn: Option Bytes) (pNext: PathSecrets Bytes l) (ppk: PrePathKEM Bytes (l+1))
  (h: pathSecretsToPrePathkem (.node opn pNext) = .success ppk):
  ∃ oppk ppkNext, ppk = .node oppk ppkNext ∧ pathSecretsToPrePathkem pNext = .success ppkNext ∧
    oppk.isSome = opn.isSome ∧
    ∀ pathSecret ∈ opn, ∃ pk ∈ oppk, ∃ sk, deriveKeypairFromPathSecret pathSecret = .success (sk, pk.val)
:= by
  cases opn with
  | none =>
    simp only [pathSecretsToPrePathkem, Result.bind_eq_success, Result.pure_eq_success] at h
    grind
  | some pathSecret =>
    simp only [pathSecretsToPrePathkem, Result.bind_eq_success, Result.pure_eq_success, mkMlsBytes_eq_success] at h
    obtain ⟨ppkNext, h1, ⟨sk, _⟩, h2, pk, rfl, rfl⟩ := h
    refine ⟨some pk, ppkNext, rfl, h1, rfl, ?_⟩
    simp [h2]

/--
Port of `pathsync_pre_pathkem_rel_to_pathsync_pathkem_rel`.
MLS*'s refinement `treekem_invariant tk` is not needed: it is only used to call `encrypt_path_secrets`,
whose precondition is not ported.
-/
theorem pathsyncPrePathkemRel_to_pathsyncPathkemRel {l: Nat}
  (ps: PathSync Bytes tkt l) (p: PathSecrets Bytes l) (pk: PathKEM Bytes l) (tk: TreeKEM Bytes l) (li: Nat)
  (groupContext: GroupContext Bytes) (rand: Randomness Bytes) (priv: TreeKEMPriv Bytes l)
  (h: encryptPathSecrets tk li p groupContext rand = .success (pk, priv))
  (hrel: pathsyncPathSecretsRel ps p):
  pathsyncPathkemRel ps pk
:= by
  obtain ⟨ppk, hppk, hrel⟩ := hrel
  unfold pathsyncPathkemRel
  induction tk using Tree.childInduction li generalizing rand with
  | leaf tk =>
    cases ps; cases p; cases pk
    obtain ⟨sk, hsk⟩ := encryptPathSecrets_zero _ _ _ _ _ _ _ h
    obtain ⟨sk', hsk'⟩ := pathSecretsToPrePathkem_getPathLeaf _ _ hppk
    have := Path.Rel.getPathLeaf hrel
    simp_all [Path.Rel, Path.getPathLeaf]
    rfl
  | node tk ih =>
    cases ps with | node opns psNext =>
    cases p with | node opn pNext =>
    obtain ⟨oupn, pkNext, optSk, privNext, rand', h1, rfl, rfl, hsome, hkey⟩ := encryptPathSecrets_succ _ _ _ _ _ _ _ _ h
    obtain ⟨oppk, ppkNext, rfl, h2, hsome', hkey'⟩ := pathSecretsToPrePathkem_node _ _ _ hppk
    obtain ⟨hrelNext, hnode⟩ := hrel
    subst opns
    refine ⟨ih _ _ _ _ _ h1 _ h2 hrelNext, ?_⟩
    cases opn <;> cases oppk <;> cases oupn <;> simp_all
    grind

/-- Port of `create_commit_state_rel`. -/
public
theorem createCommit_stateRel {st: TreeSyncState Bytes tkt TokenT groupId} {liTs: Nat} {pTs: PathSync Bytes tkt st.levels}
  (tsPend: TreeSync.API.PendingCommit st liTs pTs) (token: TokenT)
  (stTk: TreeKEMTreeState Bytes leafInd) (tkPend: TreeKEM.API.Tree.PendingCommit stTk)
  (addedLeaves: List Nat) (groupContext: GroupContext Bytes) (randFinalize: Randomness Bytes)
  (resTs: TreeSyncState Bytes tkt TokenT groupId) (resTk: TreeKEM.API.Tree.CreateCommitResult stTk)
  (hTs: TreeSync.API.finalizeCommit tsPend token = .success resTs)
  (hTk: TreeKEM.API.Tree.finalizeCreateCommit tkPend addedLeaves groupContext randFinalize = .success resTk)
  (hli: liTs = leafInd) (hrel: treesyncTreekemStateRel st stTk) (hp: pathsyncPathSecretsRel pTs tkPend.pathSecrets):
  treesyncTreekemStateRel resTs resTk.newState
:= by
  obtain ⟨newTree, h1, rfl⟩ := TreeSync.API.finalizeCommit_success tsPend token resTs hTs
  obtain ⟨newPriv, h2, hres⟩ := TreeKEM.API.Tree.finalizeCreateCommit_success tkPend addedLeaves groupContext randFinalize resTk hTk
  rw [hres]
  induction st, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  subst hli
  have hpk := pathsyncPrePathkemRel_to_pathsyncPathkemRel _ _ _ _ _ _ _ _ h2 hp
  exact treesyncTreekemStateRel_mk _ _ _ _ (applyPath_treesyncTreekemRel _ _ _ _ _ _ h1 rfl hpk)

/-- Port of `pathsync_external_pathsync_path_secrets_rel_lemma`. -/
public
theorem pathsyncExternalPathsyncPathSecretsRel_lemma {l: Nat}
  (psync: PathSync Bytes tkt l) (epsync: ExternalPathSync Bytes tkt l) (ps: PathSecrets Bytes l)
  (h1: externalPathsyncPathSecretsRel epsync ps) (h2: externalPathsyncPathsyncRel epsync psync):
  pathsyncPathSecretsRel psync ps
:= by
  obtain ⟨ppk, hppk, hrel⟩ := h1
  refine ⟨ppk, hppk, ?_⟩
  apply Path.Rel.symm_trans hrel h2 <;> grind

/-- Port of `external_path_to_path_external_pathsync_pathsync_rel_aux`. -/
theorem externalPathToPath_externalPathsyncPathsyncRel_aux {tkt: TreeKEMTypes Bytes} {l: Nat} (p: ExternalPathSync Bytes tkt l) (ln: LeafNode Bytes tkt)
  (h: ln.data.content = p.getPathLeaf.content):
  externalPathsyncPathsyncRel p (p.setPathLeaf ln)
:=
  Path.rel_setPathLeaf p ln (fun _ => rfl) h.symm

/--
Port of `external_path_to_path_external_pathsync_pathsync_rel`.
MLS*'s conjunct `(get_path_leaf pathsync).data.source = LNS_commit` follows from the last one.
-/
theorem externalPathToPath_externalPathsyncPathsyncRel {tkt: TreeKEMTypes Bytes} {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes) (signatureKey signatureNonce: Bytes)
  (res: PathSync Bytes tkt l) (h: externalPathToPath t li p groupId signatureKey signatureNonce = .success res)
  (_hsource: p.getPathLeaf.source = .update):
  externalPathsyncPathsyncRel p res ∧
  ∃ parentHash, res.getPathLeaf.data = { p.getPathLeaf with source := .commit, lifetime := (), parentHash }
:= by
  simp only [externalPathToPath, Result.bind_eq_success, Result.pure_eq_success] at h
  obtain ⟨ln, h1, rfl⟩ := h
  obtain ⟨parentHash, hln⟩ := externalPathToPathAux_data _ _ _ _ _ _ _ h1
  refine ⟨?_, parentHash, ?_⟩
  · apply externalPathToPath_externalPathsyncPathsyncRel_aux
    rw [hln]
  · simp [hln]

/-- Port of `authenticate_external_path_external_pathsync_pathsync_rel`. -/
public
theorem authenticateExternalPath_externalPathsyncPathsyncRel {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}
  (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat) (p: ExternalPathSync Bytes tkt st.levels)
  (signatureKey signatureNonce: Bytes) (res: PathSync Bytes tkt st.levels)
  (h: API.authenticateExternalPath st li p signatureKey signatureNonce = .success res)
  (hsource: p.getPathLeaf.source = .update):
  externalPathsyncPathsyncRel p res ∧
  ∃ parentHash, res.getPathLeaf.data = { p.getPathLeaf with source := .commit, lifetime := (), parentHash }
:=
  externalPathToPath_externalPathsyncPathsyncRel st.tree li p groupId signatureKey signatureNonce res h hsource

/-- Port of `get_path_leaf_pathsync_path_secrets_rel`. -/
public
theorem getPathLeaf_pathsyncPathSecretsRel {l: Nat} (psync: PathSync Bytes tkt l) (ps: PathSecrets Bytes l)
  (h: pathsyncPathSecretsRel psync ps):
  ∃ sk, CryptoBytes.hpkeGenKeypair ps.getPathLeaf = .success (sk, psync.getPathLeaf.data.content.val)
:= by
  obtain ⟨ppk, h1, hrel⟩ := h
  rw [getPathLeaf_pathsyncPrePathkemRel _ _ hrel]
  exact pathSecretsToPrePathkem_getPathLeaf _ _ h1

end State

end CryptoBytes

end MLS
