module

public import MLS.TreeSync.Proofs.API
public import MLS.TreeSync.Proofs.Operations

/-!
Port of `MLS.TreeSync.API.LeafAt`: how the `finalize_*` functions of the TreeSync API change the leaves of the tree.

Port-specific differences:
- `tree_add_only_rel` is not opaque: `grind` only unfolds it when given its definition.
- The tree of a state is not at position `0` (MLS*'s `treesync bytes tkt l 0`):
  `leafAtNat_finalizeWelcome` states the leaves of the tree with `leafAtNat t li` instead of `if li < pow2 l then leaf_at t li`.
- The implicit leaf indices `li: treesync_index st` of the pending states are hypotheses `st.tree.containsLeafIndex li`.
-/

namespace MLS.TreeSync.API

open Comparse
open MLS MLS.TreeSync

/-- Port of `leaf_at_nat`. -/
@[expose]
public
def leafAtNat {Leaf Node: Type} {l: Nat} (t: Tree (Option Leaf) Node l) (li: Nat): Option Leaf :=
  if t.containsLeafIndex li then leafAt t li else none

/-- Truncating a tree whose right subtree is empty does not change its leaves. -/
theorem leafAtNat_treeTruncate {Leaf Node: Type} {l: Nat} (t: Tree (Option Leaf) (Option Node) (l+1)) (li: Nat)
  (h: isTreeEmpty t.right):
  leafAtNat (treeTruncate t) li = leafAtNat t li
:= by
  have := leafAt_of_isTreeEmpty t.right li h
  grind [leafAtNat, treeTruncate, leafAt.eq_def, Tree.containsLeafIndex]

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}

/--
Port of `tree_add_only_rel`:
the leaves of `t2` are those of `t1`, except for some blank leaves of `t1` filled with key packages.
-/
@[expose]
public
def treeAddOnlyRel {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2): Prop :=
  ∀ li, leafAtNat t1 li = leafAtNat t2 li ∨
    (leafAtNat t1 li = none ∧ ∃ ln, leafAtNat t2 li = some ln ∧ ln.data.source = .keyPackage)

/-- Port of `tree_add_only_rel_reflexive`. -/
public
theorem treeAddOnlyRel_reflexive {l: Nat} (t: TreeSync Bytes tkt l):
  treeAddOnlyRel t t
:= by
  grind [treeAddOnlyRel]

/-- Port of `tree_add_only_rel_transitive`. -/
public
theorem treeAddOnlyRel_transitive {l1 l2 l3: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2) (t3: TreeSync Bytes tkt l3)
  (h12: treeAddOnlyRel t1 t2) (h23: treeAddOnlyRel t2 t3):
  treeAddOnlyRel t1 t3
:= by
  grind [treeAddOnlyRel]

/-- Port of `leaf_at_finalize_create`. -/
public
theorem leafAtNat_finalizeCreate {ln: LeafNode Bytes tkt} (pend: PendingCreate groupId ln) (token: TokenT) (li: Nat):
  leafAtNat (finalizeCreate pend token).tree li = if li = 0 then some ln else none
:= by
  grind [leafAtNat, finalizeCreate, treeCreate, leafAt.eq_def, Tree.containsLeafIndex]

/--
Port of `leaf_at_finalize_welcome`.
MLS*'s `t` is at position `0`, and the leaves are `if li < pow2 l then leaf_at t li else None`;
here, they are `leafAtNat t li` for `t` at any position.
MLS* requires `List.Tot.length tokens == pow2 l`, which the proof does not need.
-/
public
theorem leafAtNat_finalizeWelcome {l: Nat} {t: TreeSync Bytes tkt l}
  (pend: PendingWelcome groupId t) (tokens: List (Option TokenT)) (li: Nat):
  leafAtNat (finalizeWelcome pend tokens).tree li = leafAtNat t li
:=
  rfl

/-- Port of `leaf_at_finalize_add`. -/
public
theorem leafAtNat_finalizeAdd {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (pend: PendingAdd st ln) (token: TokenT) (li: Nat)
  (newState: TreeSyncState Bytes tkt TokenT groupId) (addLi: Nat) (h: finalizeAdd pend token = .success (newState, addLi)):
  leafAtNat st.tree addLi = none ∧
  leafAtNat newState.tree li = if li = addLi then some ln else leafAtNat st.tree li
:= by
  rcases finalizeAdd_success pend token newState addLi h with ⟨heq, newTree, h1, rfl⟩ | ⟨-, heq, newTree, h1, rfl⟩ <;>
    have := findEmptyLeaf_spec _ _ heq <;>
    have := leafAt_treeAdd _ addLi ln li newTree h1 <;>
    simp only [stateUpdateTree]
  · grind [leafAtNat, Tree.containsLeafIndex]
  · have := leafAt_treeExtend st.tree addLi
    have := leafAt_treeExtend st.tree li
    grind [leafAtNat, Tree.containsLeafIndex, treeExtend]

/-- Port of `tree_add_only_rel_finalize_add`. -/
public
theorem treeAddOnlyRel_finalizeAdd {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (pend: PendingAdd st ln) (token: TokenT)
  (newState: TreeSyncState Bytes tkt TokenT groupId) (addLi: Nat) (h: finalizeAdd pend token = .success (newState, addLi))
  (hpend: pend.Valid):
  treeAddOnlyRel st.tree newState.tree
:= by
  intro li
  have := leafAtNat_finalizeAdd pend token li newState addLi h
  grind [PendingAdd.Valid]

/-- Port of `leaf_at_finalize_update`. MLS* requires `li: treesync_index st` (here `hli`). -/
public
theorem leafAtNat_finalizeUpdate {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt} {li: Nat}
  (pend: PendingUpdate st ln li) (token: TokenT) (li': Nat)
  (hli: st.tree.containsLeafIndex li):
  leafAtNat (finalizeUpdate pend token).tree li' = if li = li' then some ln else leafAtNat st.tree li'
:= by
  have := leafAt_treeUpdate st.tree li ln li' hli
  simp only [finalizeUpdate, stateUpdateTree]
  grind [leafAtNat, Tree.containsLeafIndex, treeUpdate]

/-- Port of `leaf_at_fully_truncate_state`. -/
public
theorem leafAtNat_fullyTruncateState (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat):
  leafAtNat (fullyTruncateState st).tree li = leafAtNat st.tree li
:= by
  apply fullyTruncateState_preserves (fun st' => leafAtNat st'.tree li = leafAtNat st.tree li) _ st rfl
  grind [leafAtNat_treeTruncate]

/-- Port of `leaf_at_finalize_remove`. MLS* requires `li: treesync_index st` (here `hli`). -/
public
theorem leafAtNat_finalizeRemove {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat}
  (pend: PendingRemove st li) (li': Nat)
  (hli: st.tree.containsLeafIndex li):
  leafAtNat (finalizeRemove pend).tree li' = if li = li' then none else leafAtNat st.tree li'
:= by
  have := leafAt_treeRemove st.tree li li' hli
  simp only [finalizeRemove, leafAtNat_fullyTruncateState, stateUpdateTree]
  grind [leafAtNat, Tree.containsLeafIndex, treeRemove]

/-- Port of `leaf_at_finalize_commit`. MLS* requires `li: treesync_index st` (here `hli`). -/
public
theorem leafAtNat_finalizeCommit {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} {p: PathSync Bytes tkt st.levels}
  (pend: PendingCommit st li p) (token: TokenT) (li': Nat)
  (newState: TreeSyncState Bytes tkt TokenT groupId) (h: finalizeCommit pend token = .success newState)
  (hli: st.tree.containsLeafIndex li):
  leafAtNat newState.tree li' = if li = li' then some p.getPathLeaf else leafAtNat st.tree li'
:= by
  obtain ⟨newTree, h1, rfl⟩ := finalizeCommit_success pend token newState h
  have := leafAt_applyPathAux st.tree li p _ li' newTree h1 hli
  simp only [stateUpdateTree]
  grind [leafAtNat, Tree.containsLeafIndex, applyPath]

end CryptoBytes

end MLS.TreeSync.API
