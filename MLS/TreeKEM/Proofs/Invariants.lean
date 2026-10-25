import MLS.Common.Proofs.Result
import MLS.Common.Proofs.TreeCommon
import MLS.TreeKEM.Code.Operations
import MLS.Glue.Proofs.NetworkBinder.Properties

/-!
Port of `MLS.TreeKEM.Invariants` and `MLS.TreeKEM.Invariants.Proofs`.

Port-specific differences:
- Both modules are in this file (`MLS.TreeKEM.Invariants.Proofs` would also be `Proofs/Invariants.lean`).
- `treekemPrivInvariant t li p` takes the leaf index `li` of the private path `p` explicitly
  (implicit in MLS*'s `treekem_priv p`), and includes MLS*'s `li: leaf_index l i` (`t.containsLeafIndex li`).
- `path_filtering_weak_ok` and its lemmas (`weaken_path_filtering_ok`, `path_filtering_weak_ok_un_add`,
  `is_tree_empty_un_add`) are not ported: they are only needed for the refinements of `get_path_secret`.
- The lemmas about un-adding (`treekem_invariant_un_add`, …) are not ported:
  the un-added tree is only used to compute the encryptions, never stored in a state.
-/

namespace MLS.TreeKEM

open Comparse
open MLS

variable {Bytes: Type}

/-! ## Definitions -/

/--
Port of `unmerged_leaf_exists`.
-/
def unmergedLeafExists {l: Nat} (t: TreeKEM Bytes l) (li: Nat): Prop :=
  t.containsLeafIndex li ∧ (leafAt t li).isSome

/-- Port of `treekem_invariant`. -/
def treekemInvariant {l: Nat} (t: TreeKEM Bytes l): Prop :=
  match t.intoLeftRightView with
  | .leaf _ _ => True
  | .node opn left right =>
    (∀ pn ∈ opn, ∀ x ∈ pn.unmergedLeaves, unmergedLeafExists t x) ∧
    treekemInvariant left ∧ treekemInvariant right
termination_by l

/--
Port of `treekem_priv_invariant`.
TODO (as in MLS*): and contain public key of (get_path_leaf p) ?
-/
def treekemPrivInvariant {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (_p: TreeKEMPriv Bytes l): Prop :=
  t.containsLeafIndex li ∧ (leafAt t li).isSome

/-! ## Unfolding lemmas -/

theorem treekemInvariant_zero (t: TreeKEM Bytes 0): treekemInvariant t := by
  obtain ⟨_, bt⟩ := t
  cases bt
  rw [treekemInvariant.eq_def]
  trivial

theorem treekemInvariant_left_right {l: Nat} (t: TreeKEM Bytes (l+1)):
  treekemInvariant t ↔
    (∀ pn ∈ t.nodeContent, ∀ x ∈ pn.unmergedLeaves, unmergedLeafExists t x) ∧
    treekemInvariant t.left ∧ treekemInvariant t.right
:= by
  obtain ⟨_, bt⟩ := t
  cases bt
  rw [treekemInvariant.eq_def]
  rfl

theorem treekemInvariant_succ {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat):
  treekemInvariant t ↔
    (∀ pn ∈ t.nodeContent, ∀ x ∈ pn.unmergedLeaves, unmergedLeafExists t x) ∧
    treekemInvariant (t.child li) ∧ treekemInvariant (t.sibling li)
:= by
  grind [treekemInvariant_left_right]

theorem treekemInvariant_mkBlankTreeGeneral (l p: Nat):
  treekemInvariant (mkBlankTreeGeneral l p none none: TreeKEM Bytes l)
:= by
  induction l generalizing p with
  | zero => exact treekemInvariant_zero _
  | succ l ih => simp_all [treekemInvariant_left_right, mkBlankTreeGeneral]

/-! ## Projections of `treeAdd` and `treeApplyPath` -/

theorem treeAdd_zero (t: TreeKEM Bytes 0) (li: Nat) (lp: TreeKEMLeaf Bytes):
  treeAdd t li lp = (ChildSiblingView.leaf (some lp) t.position).pack
:= by
  rw [treeAdd.eq_def]
  simp

theorem treeAdd_succ {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (lp: TreeKEMLeaf Bytes):
  treeAdd t li lp =
    (ChildSiblingView.node
      (t.nodeContent.map fun content => { content with unmergedLeaves := insertSorted li content.unmergedLeaves })
      (treeAdd (t.child li) li lp) (t.sibling li)).pack
:= by
  rw [treeAdd.eq_def]
  simp

@[simp] theorem treeAdd_position {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes):
  (treeAdd t li lp).position = t.position
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp [treeAdd_zero]
  | node t ih => rw [treeAdd_succ]; simp [ih]

@[simp] theorem child_treeAdd {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (lp: TreeKEMLeaf Bytes):
  (treeAdd t li lp).child li = treeAdd (t.child li) li lp
:= by
  rw [treeAdd_succ]
  simp

@[simp] theorem sibling_treeAdd {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (lp: TreeKEMLeaf Bytes):
  (treeAdd t li lp).sibling li = t.sibling li
:= by
  rw [treeAdd_succ]
  simp

@[simp] theorem nodeContent_treeAdd {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (lp: TreeKEMLeaf Bytes):
  (treeAdd t li lp).nodeContent =
    t.nodeContent.map fun content => { content with unmergedLeaves := insertSorted li content.unmergedLeaves }
:= by
  rw [treeAdd_succ]
  simp

@[simp] theorem unAddP_position {l: Nat} (t: TreeKEM Bytes l) (pred: Nat → Bool):
  (unAddP t pred).position = t.position
:= by
  induction t using Tree.leftRightInduction <;> unfold unAddP <;> simp_all

/-- Port of `leaf_at_tree_add`. -/
theorem leafAt_treeAdd {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes) (li': Nat)
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt (treeAdd t li lp) li' = if li = li' then some lp else leafAt t li'
:= by
  induction t, hli, hli' using Tree.commonPathInduction li li' with
  | leaf t => rw [treeAdd_zero]; unfold leafAt; simp_all
  | _ t => rw [treeAdd_succ]; grind [leafAt.eq_def, treeAdd_position]

section BytesLike

variable [BytesLike Bytes]

theorem treeApplyPath_zero (t: TreeKEM Bytes 0) (li: Nat) (p: PathKEM Bytes 0):
  treeApplyPath t li p = (ChildSiblingView.leaf (some p.getPathLeaf) t.position).pack
:= by
  cases p
  rw [treeApplyPath.eq_def]
  simp [Path.getPathLeaf]

theorem treeApplyPath_succ {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (oupn: Option (UpdatePathNode Bytes)) (pNext: PathKEM Bytes l):
  treeApplyPath t li (.node oupn pNext) =
    (ChildSiblingView.node (oupn.map fun upn => { publicKey := upn.encryptionKey.val, unmergedLeaves := [] })
      (treeApplyPath (t.child li) li pNext) (t.sibling li)).pack
:= by
  rw [treeApplyPath.eq_def]
  simp

@[simp] theorem treeApplyPath_position {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathKEM Bytes l):
  (treeApplyPath t li p).position = t.position
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp [treeApplyPath_zero]
  | node t ih => cases p; rw [treeApplyPath_succ]; simp [ih]

/-- Port of `leaf_at_tree_apply_path`. -/
theorem leafAt_treeApplyPath {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathKEM Bytes l) (li': Nat)
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt (treeApplyPath t li p) li' = if li = li' then some p.getPathLeaf else leafAt t li'
:= by
  induction t, hli, hli' using Tree.commonPathInduction li li' with
  | leaf t => rw [treeApplyPath_zero]; unfold leafAt; simp_all
  | _ t =>
    cases p
    rw [treeApplyPath_succ]
    grind [leafAt.eq_def, Path.getPathLeaf, treeApplyPath_position]

end BytesLike

/-! ## Invariant theorems -/

/-- `treekemInvariant` with the property of unmerged leaves on the root as an hypothesis. -/
theorem treekemInvariant_intro {l: Nat} (t t': TreeKEM Bytes (l+1)) (li: Nat)
  (hnode: ∀ pn ∈ t'.nodeContent, ∀ x ∈ pn.unmergedLeaves, unmergedLeafExists t' x)
  (hchild: treekemInvariant (t'.child li)) (hsibling: t'.sibling li = t.sibling li) (hinv: treekemInvariant t):
  treekemInvariant t'
:= by
  rw [treekemInvariant_succ t' li]
  rw [treekemInvariant_succ t li] at hinv
  exact ⟨hnode, hchild, hsibling ▸ hinv.2.2⟩

theorem unmergedLeafExists_treeAdd {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes) (x: Nat)
  (hli: t.containsLeafIndex li) (hx: x = li ∨ unmergedLeafExists t x):
  unmergedLeafExists (treeAdd t li lp) x
:= by
  unfold unmergedLeafExists at *
  grind [leafAt_treeAdd, Tree.containsLeafIndex, treeAdd_position]

/-- Port of `treekem_invariant_add`. -/
theorem treekemInvariant_treeAdd {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes)
  (hli: t.containsLeafIndex li) (hinv: treekemInvariant t):
  treekemInvariant (treeAdd t li lp)
:= by
  induction t using Tree.childInduction li with
  | leaf t => exact treekemInvariant_zero _
  | node t ih =>
    apply treekemInvariant_intro t _ li _ _ (sibling_treeAdd t li lp) hinv
    · simp only [nodeContent_treeAdd, Option.mem_def, Option.map_eq_some_iff]
      rintro _ ⟨pn, hpn, rfl⟩ x hx
      apply unmergedLeafExists_treeAdd t li lp x hli
      grind [treekemInvariant_succ]
    · rw [child_treeAdd]
      exact ih (Tree.mem_child_self t hli) ((treekemInvariant_succ t li).mp hinv).2.1

/-- Port of `treekem_priv_invariant_add`. -/
theorem treekemPrivInvariant_treeAdd {l: Nat} (t: TreeKEM Bytes l) (myLi: Nat) (p: TreeKEMPriv Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes)
  (hli: t.containsLeafIndex li) (hinv: treekemPrivInvariant t myLi p):
  treekemPrivInvariant (treeAdd t li lp) myLi p
:=
  unmergedLeafExists_treeAdd t li lp myLi hli (.inr hinv)

/-- Port of `treekem_invariant_change_path`. -/
theorem treekemInvariant_treeChangePath {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (content: Option (TreeKEMLeaf Bytes))
  (hinv: treekemInvariant t):
  treekemInvariant (treeChangePath t li content none)
:= by
  induction t using Tree.childInduction li with
  | leaf t => exact treekemInvariant_zero _
  | node t ih =>
    apply treekemInvariant_intro t _ li _ _ (sibling_treeChangePath t li content none) hinv
    · simp
    · rw [child_treeChangePath]
      exact ih ((treekemInvariant_succ t li).mp hinv).2.1

/-- Port of `treekem_priv_invariant_change_path`. -/
theorem treekemPrivInvariant_treeChangePath {l: Nat} (t: TreeKEM Bytes l) (myLi: Nat) (p: TreeKEMPriv Bytes l)
  (li: Nat) (content: Option (TreeKEMLeaf Bytes))
  (hli: t.containsLeafIndex li) (hne: li ≠ myLi) (hinv: treekemPrivInvariant t myLi p):
  treekemPrivInvariant (treeChangePath t li content none) myLi p
:= by
  unfold treekemPrivInvariant at *
  grind [leafAt_treeChangePath, Tree.containsLeafIndex]

/-- Port of `treekem_invariant_update`. -/
theorem treekemInvariant_treeUpdate {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes)
  (hinv: treekemInvariant t):
  treekemInvariant (treeUpdate t li lp)
:=
  treekemInvariant_treeChangePath t li (some lp) hinv

/-- Port of `treekem_invariant_remove`. -/
theorem treekemInvariant_treeRemove {l: Nat} (t: TreeKEM Bytes l) (li: Nat)
  (hinv: treekemInvariant t):
  treekemInvariant (treeRemove t li)
:=
  treekemInvariant_treeChangePath t li none hinv

/-- Port of `treekem_invariant_extend`. -/
theorem treekemInvariant_treeExtend {l: Nat} (t: TreeKEM Bytes l) (hinv: treekemInvariant t):
  treekemInvariant (treeExtend t)
:= by
  simp [treekemInvariant_left_right, treeExtend, mkBlankTree, hinv, treekemInvariant_mkBlankTreeGeneral]

/-- Port of `treekem_priv_invariant_extend`. -/
theorem treekemPrivInvariant_treeExtend {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: TreeKEMPriv Bytes l)
  (hinv: treekemPrivInvariant t li p):
  treekemPrivInvariant (treeExtend t) li (pathExtend p)
:= by
  unfold treekemPrivInvariant at *
  grind [leafAt_treeExtend, treeExtend, Tree.containsLeafIndex]

/-- Port of `treekem_invariant_truncate`. -/
theorem treekemInvariant_treeTruncate {l: Nat} (t: TreeKEM Bytes (l+1)) (hinv: treekemInvariant t):
  treekemInvariant (treeTruncate t)
:= by
  grind [treekemInvariant_left_right, treeTruncate]

/--
Port of `treekem_priv_invariant_truncate`.
MLS* requires `li: leaf_index (l-1) 0` (here `hli`).
-/
theorem treekemPrivInvariant_treeTruncate {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (p: TreeKEMPriv Bytes (l+1))
  (hli: li < t.position + 2^l) (hinv: treekemPrivInvariant t li p):
  treekemPrivInvariant (treeTruncate t) li (pathTruncate p)
:= by
  unfold treekemPrivInvariant at *
  rw [leafAt.eq_def t] at hinv
  grind [treeTruncate]

section BytesLike

variable [BytesLike Bytes]

/-- Port of `treekem_invariant_apply_path`. -/
theorem treekemInvariant_treeApplyPath {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathKEM Bytes l)
  (hinv: treekemInvariant t):
  treekemInvariant (treeApplyPath t li p)
:= by
  induction t using Tree.childInduction li with
  | leaf t => exact treekemInvariant_zero _
  | node t ih =>
    cases p with | node oupn pNext =>
    rw [treeApplyPath_succ]
    apply treekemInvariant_intro t _ li _ _ (by simp) hinv
    · cases oupn <;> simp
    · simpa using ih pNext ((treekemInvariant_succ t li).mp hinv).2.1

/-- Port of `treekem_priv_invariant_apply_path` (for any new private path). -/
theorem treekemPrivInvariant_treeApplyPath {l: Nat} (t: TreeKEM Bytes l) (myLi: Nat) (priv priv': TreeKEMPriv Bytes l)
  (li: Nat) (p: PathKEM Bytes l)
  (hli: t.containsLeafIndex li) (hinv: treekemPrivInvariant t myLi priv):
  treekemPrivInvariant (treeApplyPath t li p) myLi priv'
:= by
  unfold treekemPrivInvariant at *
  grind [leafAt_treeApplyPath, Tree.containsLeafIndex, treeApplyPath_position]

end BytesLike

/-! ## Create commit invariants -/

section CryptoBytes

variable [CryptoBytes Bytes]

theorem generatePathSecrets_succ {l: Nat} (t: TreeKEM Bytes (l+1)) (leafSk pathSecret0: Bytes) (li: Nat)
  (p: PathSecrets Bytes (l+1)) (commitSecret: Bytes)
  (h: generatePathSecrets t leafSk pathSecret0 li = .success (p, commitSecret)):
  ∃ pNext myPathSecret,
    generatePathSecrets (t.child li) leafSk pathSecret0 li = .success (pNext, myPathSecret) ∧
    p = .node (if !isTreeEmpty (t.sibling li) then some myPathSecret else none) pNext
:= by
  rw [generatePathSecrets.eq_def] at h
  simp only [Tree.intoChildSiblingView_eq, Result.bind_eq_success] at h
  obtain ⟨⟨pNext, myPathSecret⟩, h1, h2⟩ := h
  refine ⟨pNext, myPathSecret, ?_⟩
  split at h2 <;> simp_all

/-- Port of `path_filtering_ok_generate_path_secrets`. -/
theorem pathFilteringOk_generatePathSecrets {l: Nat} (t: TreeKEM Bytes l) (leafSk pathSecret0: Bytes) (li: Nat)
  (p: PathSecrets Bytes l) (commitSecret: Bytes)
  (h: generatePathSecrets t leafSk pathSecret0 li = .success (p, commitSecret)):
  pathFilteringOk t li p
:= by
  induction t using Tree.childInduction li generalizing commitSecret with
  | leaf t => simp
  | node t ih =>
    obtain ⟨pNext, myPathSecret, h1, rfl⟩ := generatePathSecrets_succ t leafSk pathSecret0 li p commitSecret h
    cases h': isTreeEmpty (t.sibling li) <;> simp_all

theorem encryptPathSecrets_succ {l: Nat} (t: TreeKEM Bytes (l+1)) (li: Nat) (opn: Option Bytes) (pNext: PathSecrets Bytes l)
  (groupContext: GroupContext Bytes) (rand: Randomness Bytes) (res: PathKEM Bytes (l+1)) (priv: TreeKEMPriv Bytes (l+1))
  (h: encryptPathSecrets t li (.node opn pNext) groupContext rand = .success (res, priv)):
  ∃ oupn resNext optSk privNext rand',
    encryptPathSecrets (t.child li) li pNext groupContext rand' = .success (resNext, privNext) ∧
    res = .node oupn resNext ∧ priv = .node optSk privNext ∧ oupn.isSome = opn.isSome
:= by
  rw [encryptPathSecrets.eq_def] at h
  cases opn <;> simp only [Tree.intoChildSiblingView_eq, Result.bind_eq_success, Result.pure_eq_success] at h <;> grind

/--
Port of `path_filtering_ok_encrypt_path_secrets`.
`refT` corresponds to the actual tree, which is used to compute filtered nodes,
`t` corresponds to the un-added tree, used to perform encryption.
MLS* requires that `t` and `refT` are at the same position (by typing, here `hpos`).
-/
theorem pathFilteringOk_encryptPathSecrets {l: Nat} (refT t: TreeKEM Bytes l) (li: Nat) (p: PathSecrets Bytes l)
  (groupContext: GroupContext Bytes) (rand: Randomness Bytes) (res: PathKEM Bytes l) (priv: TreeKEMPriv Bytes l)
  (h: encryptPathSecrets t li p groupContext rand = .success (res, priv))
  (hpos: refT.position = t.position) (hfilter: pathFilteringOk refT li p):
  pathFilteringOk refT li res
:= by
  induction refT using Tree.childInduction li generalizing rand with
  | leaf refT => simp
  | node refT ih =>
    cases p with | node opn pNext =>
    obtain ⟨oupn, resNext, optSk, privNext, rand', h1, rfl, rfl, hsome⟩ :=
      encryptPathSecrets_succ t li opn pNext groupContext rand res priv h
    simp only [pathFilteringOk_succ, Bool.and_eq_true] at hfilter ⊢
    refine ⟨by grind [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none], ?_⟩
    exact ih (t.child li) pNext rand' resNext privNext h1 (by grind) hfilter.2

end CryptoBytes

end MLS.TreeKEM
