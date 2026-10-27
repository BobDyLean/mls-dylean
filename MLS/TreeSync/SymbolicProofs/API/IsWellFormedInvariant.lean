module

public import MLS.TreeSync.SymbolicProofs.IsWellFormed
public import MLS.TreeSync.Code.API
public import MLS.TreeSync.Proofs.API

/-!
Port of `MLS.TreeSync.Symbolic.API.IsWellFormedInvariant`: well-formedness of the trees computed by the TreeSync API.

Port-specific differences:
- MLS*'s `is_well_formed_*` lemmas are `*_wf`; they take the result with a success hypothesis.
-/

namespace MLS.TreeSync.API

open Comparse
open MLS MLS.TreeSync

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}
variable (pred: Bytes → Prop) [BytesCompatiblePred pred]

/-- Port of `is_well_formed_finalize_create`. -/
public
theorem finalizeCreate_wf {ln: LeafNode Bytes tkt} (pend: PendingCreate groupId ln) (token: TokenT)
  (h: (LeafNode.mf tkt).wf pred ln):
  (TreeSync.mf tkt 0).wf pred (finalizeCreate pend token).tree
:= by
  simp [finalizeCreate, treeCreate, Tree.mf.wf_zero, MlsOption.mf.wf_eq, h]

omit [BytesCompatiblePred pred] in
/--
Port of `is_well_formed_finalize_welcome`.
MLS* requires `List.Tot.length tokens == pow2 l`, which the proof does not need.
-/
public
theorem finalizeWelcome_wf {l: Nat} {t: TreeSync Bytes tkt l} (pend: PendingWelcome groupId t)
  (tokens: List (Option TokenT)) (h: (TreeSync.mf tkt l).wf pred t):
  (TreeSync.mf tkt (finalizeWelcome pend tokens).levels).wf pred (finalizeWelcome pend tokens).tree
:=
  h

/--
Port of `is_well_formed_finalize_add`.
MLS*'s `Success? (finalize_add pend token)` is the success hypothesis `hres`.
-/
public
theorem finalizeAdd_wf {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (pend: PendingAdd st ln) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId) (li: Nat)
  (hres: finalizeAdd pend token = .success (res, li))
  (hst: (TreeSync.mf tkt st.levels).wf pred st.tree) (hln: (LeafNode.mf tkt).wf pred ln):
  (TreeSync.mf tkt res.levels).wf pred res.tree
:= by
  rcases finalizeAdd_success pend token res li hres with ⟨-, newTree, h, rfl⟩ | ⟨-, -, newTree, h, rfl⟩
  · exact treeAdd_wf pred _ _ _ _ h hst hln
  · exact treeAdd_wf pred _ _ _ _ h (treeExtend_wf pred _ hst) hln

/-- Port of `is_well_formed_finalize_update`. -/
public
theorem finalizeUpdate_wf {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt} {li: Nat}
  (pend: PendingUpdate st ln li) (token: TokenT)
  (hst: (TreeSync.mf tkt st.levels).wf pred st.tree) (hln: (LeafNode.mf tkt).wf pred ln):
  (TreeSync.mf tkt (finalizeUpdate pend token).levels).wf pred (finalizeUpdate pend token).tree
:=
  treeUpdate_wf pred _ _ _ hst hln

/-- Port of `is_well_formed_fully_truncate_state`. -/
public
theorem fullyTruncateState_wf (st: TreeSyncState Bytes tkt TokenT groupId)
  (hst: (TreeSync.mf tkt st.levels).wf pred st.tree):
  (TreeSync.mf tkt (fullyTruncateState st).levels).wf pred (fullyTruncateState st).tree
:=
  fullyTruncateState_preserves (fun st => (TreeSync.mf tkt st.levels).wf pred st.tree)
    (fun tree _ _ h => treeTruncate_wf pred tree h) st hst

/-- Port of `is_well_formed_finalize_remove`. -/
public
theorem finalizeRemove_wf {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} (pend: PendingRemove st li)
  (hst: (TreeSync.mf tkt st.levels).wf pred st.tree):
  (TreeSync.mf tkt (finalizeRemove pend).levels).wf pred (finalizeRemove pend).tree
:=
  fullyTruncateState_wf pred _ (treeRemove_wf pred _ _ hst)

/--
Port of `is_well_formed_finalize_commit`.
MLS*'s `Success? (finalize_commit pend token)` is the success hypothesis `hres`.
-/
public
theorem finalizeCommit_wf {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} {p: PathSync Bytes tkt st.levels}
  (pend: PendingCommit st li p) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId)
  (hres: finalizeCommit pend token = .success res) (hcompat: PreIsHashCompatible pred)
  (hst: (TreeSync.mf tkt st.levels).wf pred st.tree) (hp: (PathSync.mf tkt st.levels).wf pred p):
  (TreeSync.mf tkt res.levels).wf pred res.tree
:= by
  obtain ⟨newTree, h, rfl⟩ := finalizeCommit_success pend token res hres
  exact applyPath_wf pred _ _ _ _ h hcompat hst hp

end MLS.TreeSync.API
