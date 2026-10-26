module

public import MLS.TreeKEM.Code.Operations
public import MLS.TreeKEM.Code.API.Tree.Types

/-!
Port of `MLS.TreeKEM.API.Tree`.

Port-specific differences:
- The invariants of the state (see `TreeKEMTreeState`) are the predicate `TreeKEMTreeState.Valid`,
  preserved by the functions of this module (see `MLS.TreeKEM.Proofs.API.Tree`).
  Preconditions of MLS* are documented in the docstrings: when they are not met,
  the functions fail or return a state that does not satisfy MLS*'s invariants.
- Trees of the state are assumed to be at position `0` (MLS*'s `treekem bytes levels 0`).
- The namespace is `MLS.TreeKEM.API.Tree` (instead of `MLS.TreeKEM`), as its names are reused by `MLS.TreeKEM.API`.
- `truncate_one` returns an `Option`, which is `none` when its precondition does not hold
  (`fully_truncate` stops there).
-/

namespace MLS.TreeKEM.API.Tree

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/-! ## Create -/

/-- Port of `create`. -/
@[expose]
public
def create (decKey: Bytes) (encKey: Bytes): TreeKEMTreeState Bytes 0 :=
  {
    levels := 0
    tree := treeCreate { publicKey := encKey }
    priv := .leaf decKey
  }

/-! ## Welcome -/

/--
Port of `welcome`.
MLS* requires `treekem_invariant t`, `leaf_ind < pow2 l` and `Some? (leaf_at t leaf_ind)`;
otherwise, the returned state does not satisfy MLS*'s invariants.
-/
@[expose]
public
def welcome {l: Nat} (t: TreeKEM Bytes l) (leafDecryptionKey: Bytes) (optPathSecretAndInviterInd: Option (Bytes × Nat)) (leafInd: Nat):
  Result (TreeKEMTreeState Bytes leafInd)
:= do
  let priv := createEmptyPriv leafDecryptionKey
  let priv ←
    match optPathSecretAndInviterInd with
    | none => pure priv
    | some (pathSecret, inviterInd) =>
      if !(leafInd != inviterInd) then
        Result.error "welcome: leaf_index and inviter index are the same"
      else if !(inviterInd < 2^l) then
        Result.error "welcome: inviter_index too big"
      else
        let pathSecretLevel := computeLeastCommonAncestorLevel t leafInd priv inviterInd
        let (priv, _) ← pathApplyPath t leafInd priv pathSecret pathSecretLevel
        pure priv
  pure {
    levels := l
    tree := t
    priv
  }

/-! ## Add -/

/-- Port of `add`. -/
@[expose]
public
def add {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (kp: TreeKEMLeaf Bytes): TreeKEMTreeState Bytes leafInd × Nat :=
  match findEmptyLeaf st.tree with
  | some i =>
    ({ st with tree := treeAdd st.tree i kp }, i)
  | none =>
    let extendedTree := treeExtend st.tree
    -- Always `some` (MLS*'s `find_empty_leaf_tree_extend`).
    let i := (findEmptyLeaf extendedTree).getD (2^st.levels)
    ({ levels := st.levels+1
       tree := treeAdd extendedTree i kp
       priv := pathExtend st.priv
    }, i)

/-! ## Update -/

/-- Port of `update_myself`. -/
@[expose]
public
def updateMyself {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (leafDecryptionKey: Bytes):
  TreeKEMTreeState Bytes leafInd
:=
  { st with
    tree := treeUpdate st.tree leafInd lp
    priv := createEmptyPriv leafDecryptionKey
  }

/--
Port of `update_other`.
MLS* requires `i < pow2 st.levels` and `i <> leaf_ind`; otherwise, see `pathBlank`.
-/
@[expose]
public
def updateOther {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (i: Nat):
  TreeKEMTreeState Bytes leafInd
:=
  { st with
    tree := treeUpdate st.tree i lp
    priv := pathBlank st.tree leafInd st.priv i
  }

/-! ## Remove -/

/--
Port of `truncate_one`.
MLS* requires `1 <= st.levels && is_tree_empty (TNode?.right st.tree)`; otherwise, this function returns `none`.
MLS* then proves that `leaf_ind < pow2 (st.levels-1)` (MLS*'s `false_elim` branch); this function returns `none` otherwise.
-/
@[expose]
public
def truncateOne {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd):
  Option {res: TreeKEMTreeState Bytes leafInd // res.levels + 1 = st.levels}
:=
  match st with
  | { levels := 0, .. } => none
  | { levels := l+1, tree, priv } =>
    if isTreeEmpty tree.right && leafInd < 2^l then
      some ⟨{ levels := l, tree := treeTruncate tree, priv := pathTruncate priv }, rfl⟩
    else
      none

/-- Port of `fully_truncate`. -/
@[expose]
public
def fullyTruncate {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd): TreeKEMTreeState Bytes leafInd :=
  match truncateOne st with
  | some ⟨st', _⟩ => fullyTruncate st'
  | none => st
termination_by st.levels

/--
Port of `remove_aux`.
MLS* requires `i < pow2 st.levels` and `i <> leaf_ind`; otherwise, see `pathBlank`.
-/
@[expose]
public
def removeAux {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (i: Nat): TreeKEMTreeState Bytes leafInd :=
  { st with
    tree := treeRemove st.tree i
    priv := pathBlank st.tree leafInd st.priv i
  }

/--
Port of `remove`.
MLS* requires `i < pow2 st.levels` and `i <> leaf_ind`; otherwise, see `pathBlank`.
-/
@[expose]
public
def remove {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (i: Nat): TreeKEMTreeState Bytes leafInd :=
  fullyTruncate (removeAux st i)

/-! ## Process Commit -/

/--
Port of `commit`.
MLS* requires `li < pow2 st.levels`, `li <> leaf_ind`, `path_filtering_ok st.tree p`
and `~(List.Tot.memP leaf_ind excluded_leaves)`; otherwise, this function may fail (see `getPathSecret`).
-/
@[expose]
public
def commit {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (li: Nat) (p: PathKEM Bytes st.levels)
  (excludedLeaves: List Nat) (groupContext: GroupContext Bytes)
  : Result (TreeKEMTreeState Bytes leafInd × Bytes)
:= do
  let unAddedTree := unAdd st.tree excludedLeaves
  if !checkUpdatePathCiphertextsLengthes unAddedTree li p then
    Result.error "TreeKEM.commit: bad UpdatePath ciphertext lengths"
  else
    let (pathSecret, leastCommonAncestorLevel) ← getPathSecret unAddedTree leafInd li st.priv p groupContext
    let newTree := treeApplyPath st.tree li p
    let (newPriv, rootSecret) ← pathApplyPath newTree leafInd st.priv pathSecret leastCommonAncestorLevel
    pure ({ st with tree := newTree, priv := newPriv }, rootSecret)

/-! ## Create Commit -/

/-- Port of `prepare_create_commit_entropy_lengths`. -/
@[expose]
public
def prepareCreateCommitEntropyLengths (Bytes: Type) [CryptoBytes Bytes]: List Nat :=
  [CryptoBytes.hpkePrivateKeyLength Bytes, CryptoBytes.kdfLength Bytes]

/--
Port of `pending_commit`.
The refinement `path_filtering_ok st.tree path_secrets` is the predicate `PendingCommit.Valid`
(in `MLS.TreeKEM.Proofs.API.Tree`); the refinement
`forget_path_secrets path_secrets == generate_forgotten_path_secrets st.tree leaf_ind` is not ported.
-/
public
structure PendingCommit {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) where
  pathSecrets: PathSecrets Bytes st.levels
  commitSecret: Bytes

/--
Port of `prepare_create_commit`.
MLS* requires `rand: randomness bytes (prepare_create_commit_entropy_lengths bytes)`;
otherwise, this function fails when there is not enough randomness.
-/
@[expose]
public
def prepareCreateCommit {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (rand: Randomness Bytes)
  : Result (PendingCommit st × PrePathKEM Bytes st.levels)
:= do
  let (leafSk, rand) ← destRandomness rand
  let (pathSecret0, _) ← destRandomness rand
  let (pathSecrets, commitSecret) ← generatePathSecrets st.tree leafSk pathSecret0 leafInd
  let preUpdPath ← pathSecretsToPrePathkem pathSecrets
  pure ({
    pathSecrets
    commitSecret
  }, preUpdPath)

/-- Port of `finalize_create_commit_entropy_lengths`. -/
@[expose]
public
def finalizeCreateCommitEntropyLengths {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (addedLeaves: List Nat): List Nat :=
  encryptPathSecretsEntropyLengths (unAdd st.tree addedLeaves) leafInd

/--
Port of `create_commit_result`.
The refinement `path_filtering_ok st.tree update_path` is the predicate `CreateCommitResult.Valid`
(in `MLS.TreeKEM.Proofs.API.Tree`).
-/
public
structure CreateCommitResult {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) where
  newState: TreeKEMTreeState Bytes leafInd
  updatePath: PathKEM Bytes st.levels
  commitSecret: Bytes
  addedLeavesPathSecrets: List Bytes

/--
Port of `finalize_create_commit`.
MLS* requires `randomness: randomness bytes (finalize_create_commit_entropy_lengths st added_leaves)`
(i.e. `finalizeCreateCommitEntropyLengths st addedLeaves`);
otherwise, this function fails when there is not enough randomness.
-/
@[expose]
public
def finalizeCreateCommit {leafInd: Nat} {st: TreeKEMTreeState Bytes leafInd}
  (pending: PendingCommit st) (addedLeaves: List Nat) (groupContext: GroupContext Bytes)
  (randomness: Randomness Bytes)
  : Result (CreateCommitResult st)
:= do
  let (updatePath, newPriv) ← encryptPathSecrets (unAdd st.tree addedLeaves) leafInd pending.pathSecrets groupContext randomness
  let addedLeavesPathSecrets ← getPathSecretOfAddedLeaves st.tree leafInd pending.pathSecrets addedLeaves
  let newTree := treeApplyPath st.tree leafInd updatePath
  pure {
    newState := { st with
      tree := newTree
      priv := newPriv
    }
    updatePath
    commitSecret := pending.commitSecret
    addedLeavesPathSecrets
  }

end MLS.TreeKEM.API.Tree
