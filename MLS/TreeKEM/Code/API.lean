module

public import MLS.TreeKEM.Code.API.Types
public import MLS.TreeKEM.Code.API.Tree
public import MLS.TreeKEM.Code.API.KeySchedule

/-!
Port of `MLS.TreeKEM.API`.

Port-specific differences:
- The namespace is `MLS.TreeKEM.API`: `MLS.TreeKEM.API.Tree` and `MLS.TreeKEM.API.KeySchedule`
  are referred to as `Tree` and `KeySchedule` (MLS*'s module abbreviations `T` and `KS`).
- The invariants of the state and the refinements of the API types are predicates `*.Valid`,
  in `MLS.TreeKEM.Proofs.API`: preconditions of MLS* are documented in the docstrings.
- `export` is a Lean keyword: the function is named `«export»`.
-/

namespace MLS.TreeKEM.API

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/-! ## Create -/

/-- Port of `create`. -/
public
def create (decKey: Bytes) (encKey: Bytes) (epochSecret: Bytes) (groupContext: GroupContext Bytes):
  Result (TreeKEMState Bytes 0 × Bytes)
:= do
  let treeState := Tree.create decKey encKey
  let (keyscheduleState, encryptionSecret) ← KeySchedule.createFromEpochSecret epochSecret groupContext
  pure ({
    treeState
    keyscheduleState
  }, encryptionSecret)

/-! ## Welcome -/

/--
Port of `welcome`.
MLS* requires `treekem_invariant t`, `leaf_ind < pow2 l` and `Some? (leaf_at t leaf_ind)`;
otherwise, see `Tree.welcome`.
-/
public
def welcome {l: Nat} (t: TreeKEM Bytes l) (leafDecryptionKey: Bytes) (optPathSecretAndInviterInd: Option (Bytes × Nat)) (leafInd: Nat)
  (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes)
  : Result (TreeKEMState Bytes leafInd × Bytes)
:= do
  let treeState ← Tree.welcome t leafDecryptionKey optPathSecretAndInviterInd leafInd
  let (keyscheduleState, encryptionSecret) ← KeySchedule.createFromJoinerSecret joinerSecret psks groupContext
  pure ({
    treeState
    keyscheduleState
  }, encryptionSecret)

/-! ## Add -/

/-- Port of `add`. -/
public
def add {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (kp: TreeKEMLeaf Bytes): TreeKEMState Bytes leafInd × Nat :=
  let (treeState, i) := Tree.add st.treeState kp
  ({ st with treeState }, i)

/-! ## Update -/

/-- Port of `update_myself`. -/
public
def updateMyself {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (leafDecryptionKey: Bytes):
  TreeKEMState Bytes leafInd
:=
  { st with treeState := Tree.updateMyself st.treeState lp leafDecryptionKey }

/--
Port of `update_other`.
MLS* requires `i < pow2 st.tree_state.levels` and `i <> leaf_ind`; otherwise, see `Tree.updateOther`.
-/
public
def updateOther {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (i: Nat): TreeKEMState Bytes leafInd :=
  { st with treeState := Tree.updateOther st.treeState lp i }

/-! ## Remove -/

/--
Port of `remove`.
MLS* requires `i < pow2 st.tree_state.levels` and `i <> leaf_ind`; otherwise, see `Tree.remove`.
-/
public
def remove {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (i: Nat): TreeKEMState Bytes leafInd :=
  { st with treeState := Tree.remove st.treeState i }

/-! ## Process Commit -/

/--
Port of `full_commit_args`.
The refinements of MLS* (`commit_leaf_ind < pow2 st.levels`, `commit_leaf_ind <> leaf_ind`,
`path_filtering_ok st.tree path` and `~(List.Tot.memP leaf_ind excluded_leaves)`) are the predicate
`FullCommitArgs.Valid` (in `MLS.TreeKEM.Proofs.API`), see `Tree.commit`.
-/
public
structure FullCommitArgs {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) where
  commitLeafInd: Nat
  path: PathKEM Bytes st.levels
  excludedLeaves: List Nat
  provisionalGroupContext: GroupContext Bytes

/-- Port of `pending_process_commit`. -/
public
structure PendingProcessCommit {leafInd: Nat} (st: TreeKEMState Bytes leafInd) where
  nextTreeState: TreeKEMTreeState Bytes leafInd
  optCommitSecret: Option Bytes

/-- Port of `prepare_process_full_commit`. -/
public
def prepareProcessFullCommit {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (args: FullCommitArgs st.treeState):
  Result (PendingProcessCommit st)
:= do
  let (nextTreeState, commitSecret) ← Tree.commit st.treeState args.commitLeafInd args.path args.excludedLeaves args.provisionalGroupContext
  pure {
    nextTreeState
    optCommitSecret := some commitSecret
  }

/-- Port of `prepare_process_add_only_commit`. -/
public
def prepareProcessAddOnlyCommit {leafInd: Nat} (st: TreeKEMState Bytes leafInd): Result (PendingProcessCommit st) :=
  pure {
    nextTreeState := st.treeState
    optCommitSecret := none
  }

/-- Port of `finalize_process_commit`. -/
public
def finalizeProcessCommit {leafInd: Nat} {st: TreeKEMState Bytes leafInd}
  (pend: PendingProcessCommit st) (psks: List (PreSharedKeyId Bytes × Bytes)) (newGroupContext: GroupContext Bytes)
  : Result (TreeKEMState Bytes leafInd × Bytes)
:= do
  let (keyscheduleState, encryptionSecret, _) ← KeySchedule.commit st.keyscheduleState pend.optCommitSecret psks newGroupContext
  pure ({
    treeState := pend.nextTreeState
    keyscheduleState
  }, encryptionSecret)

/-! ## Create Commit -/

/-- Port of `prepare_create_commit_entropy_lengths`. -/
public
def prepareCreateCommitEntropyLengths (Bytes: Type) [CryptoBytes Bytes]: List Nat :=
  Tree.prepareCreateCommitEntropyLengths Bytes

/-- Port of `pending_create_commit`. -/
public
structure PendingCreateCommit {leafInd: Nat} (st: TreeKEMState Bytes leafInd) where
  pend: Tree.PendingCommit st.treeState

/--
Port of `prepare_create_commit`.
MLS* requires `rand: randomness bytes (prepare_create_commit_entropy_lengths bytes)`;
otherwise, this function fails when there is not enough randomness.
-/
public
def prepareCreateCommit {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (rand: Randomness Bytes):
  Result (PendingCreateCommit st × PrePathKEM Bytes st.treeState.levels)
:= do
  let (pend, path) ← Tree.prepareCreateCommit st.treeState rand
  pure ({ pend }, path)

/-- Port of `continue_create_commit_entropy_lengths`. -/
public
def continueCreateCommitEntropyLengths {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (addedLeaves: List Nat): List Nat :=
  Tree.finalizeCreateCommitEntropyLengths st.treeState addedLeaves

/-- Port of `pending_create_commit_2`. -/
public
structure PendingCreateCommit2 (Bytes: Type) (leafInd: Nat) where
  newState: TreeKEMState Bytes leafInd
  commitSecret: Option Bytes

/--
Port of `continue_create_commit_result`.
The refinement `path_filtering_ok st.tree_state.tree update_path` is the predicate `ContinueCreateCommitResult.Valid`
(in `MLS.TreeKEM.Proofs.API`).
-/
public
structure ContinueCreateCommitResult {leafInd: Nat} (st: TreeKEMState Bytes leafInd) where
  updatePath: PathKEM Bytes st.treeState.levels
  addedLeavesPathSecrets: List Bytes

/--
Port of `continue_create_commit`.
MLS* requires `randomness: randomness bytes (continue_create_commit_entropy_lengths st added_leaves)`;
otherwise, this function fails when there is not enough randomness.
-/
public
def continueCreateCommit {leafInd: Nat} {st: TreeKEMState Bytes leafInd}
  (pending: PendingCreateCommit st) (addedLeaves: List Nat) (provisionalGroupContext: GroupContext Bytes)
  (randomness: Randomness Bytes)
  : Result (PendingCreateCommit2 Bytes leafInd × ContinueCreateCommitResult st)
:= do
  let treeCommitResult ← Tree.finalizeCreateCommit pending.pend addedLeaves provisionalGroupContext randomness
  let newState := { st with
    treeState := treeCommitResult.newState
  }
  pure ({
    newState
    commitSecret := some treeCommitResult.commitSecret
  }, {
    updatePath := treeCommitResult.updatePath
    addedLeavesPathSecrets := treeCommitResult.addedLeavesPathSecrets
  })

/-- Port of `prepare_create_add_only_commit`. -/
public
def prepareCreateAddOnlyCommit {leafInd: Nat} (st: TreeKEMState Bytes leafInd): Result (PendingCreateCommit2 Bytes leafInd) :=
  pure {
    newState := st
    commitSecret := none
  }

/-- Port of `create_commit_result`. -/
public
structure CreateCommitResult (Bytes: Type) (leafInd: Nat) where
  newState: TreeKEMState Bytes leafInd
  encryptionSecret: Bytes
  -- secrets needed to generate welcomes
  welcomeSecret: Bytes
  joinerSecret: Bytes

/-- Port of `finalize_create_commit`. -/
public
def finalizeCreateCommit {leafInd: Nat} (pending: PendingCreateCommit2 Bytes leafInd)
  (newGroupContext: GroupContext Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  : Result (CreateCommitResult Bytes leafInd)
:= do
  let (keyscheduleState, encryptionSecret, additionalSecrets) ← KeySchedule.commit pending.newState.keyscheduleState pending.commitSecret psks newGroupContext
  pure {
    newState := { pending.newState with keyscheduleState }
    encryptionSecret
    welcomeSecret := additionalSecrets.welcomeSecret
    joinerSecret := additionalSecrets.joinerSecret
  }

/-! ## Getters -/

/-- Port of `get_epoch_keys`. -/
public
def getEpochKeys {leafInd: Nat} (st: TreeKEMState Bytes leafInd): EpochKeys Bytes :=
  st.keyscheduleState.epochKeys

/-- Port of `export`. -/
public
def «export» {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (label: String) (context: Bytes) (len: Nat): Result Bytes :=
  KeySchedule.«export» st.keyscheduleState label context len

end MLS.TreeKEM.API
