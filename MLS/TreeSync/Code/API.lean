module

public import MLS.TreeSync.Code.API.Types
public import MLS.TreeSync.Code.Operations
public import MLS.TreeSync.Code.TreeHash
public import MLS.TreeSync.Code.Invariants.UnmergedLeaves
public import MLS.TreeSync.Code.Invariants.ParentHash
public import MLS.TreeSync.Code.Invariants.ValidLeaves
public import MLS.TreeSync.Code.Invariants.AuthService

/-!
Port of `MLS.TreeSync.API`.

Port-specific differences:
- The namespace is `MLS.TreeSync.API` (as `MLS.TreeKEM.API` and `MLS.TreeDEM.API`).
- MLS*'s `Refined` interface is not ported: the operations are the ones of `MLS.TreeSync.Operations`.
- The `pending_*` types only contain data: their refinements (`pending_*_proof`, `as_input_for`)
  are the predicates `Pending*.Valid` of `MLS.TreeSync.Proofs.API`, established by the `prepare_*` functions
  (which check them at runtime). MLS*'s refinements on trees (`treesync_valid`) are `TreeSyncState.TreeValid`.
  The `_valid` lemmas are in `MLS.TreeSync.Proofs.API`.
- `finalize_add` fails (as an internal failure) when the extended tree has no empty leaf,
  which MLS* proves impossible (`find_empty_leaf_tree_extend`).
-/

namespace MLS.TreeSync.API

open Comparse
open MLS MLS.TreeSync

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}

/-- Port of `state_update_tree`. -/
public
def stateUpdateTree {l: Nat} (_st: TreeSyncState Bytes tkt TokenT groupId) (newTree: TreeSync Bytes tkt l) (newTokens: ASTokens TokenT l):
  TreeSyncState Bytes tkt TokenT groupId
:=
  {
    levels := l
    tree := newTree
    tokens := newTokens
  }

/-! ## Create -/

/-- Port of `pending_create`. -/
public
structure PendingCreate (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt) where
  asInput: ASInput Bytes

/-- Port of `prepare_create`. -/
public
def prepareCreate (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt): Result (PendingCreate groupId ln) :=
  if !leafIsValid ln groupId 0 then
    Result.error "prepare_create: leaf node is not valid"
  else
    pure {
      asInput := leafNodeToAsInput ln
    }

/-- Port of `finalize_create`. -/
public
def finalizeCreate {ln: LeafNode Bytes tkt} (_pend: PendingCreate groupId ln) (token: TokenT): TreeSyncState Bytes tkt TokenT groupId :=
  {
    levels := 0
    tree := treeCreate ln
    tokens := treeCreate token
  }

/-! ## Welcome -/

/-- Port of `pending_welcome`. -/
public
structure PendingWelcome {l: Nat} (groupId: MlsBytes Bytes) (t: TreeSync Bytes tkt l) where
  asInputs: List (Option (ASInput Bytes))

/-- Port of `prepare_welcome`. -/
public
def prepareWelcome {l: Nat} (groupId: MlsBytes Bytes) (t: TreeSync Bytes tkt l): Result (PendingWelcome groupId t) :=
  if !unmergedLeavesOk t then
    Result.error "prepare_welcome: malformed unmerged leaves"
  else if !parentHashInvariant t then
    Result.error "prepare_welcome: bad parent hash"
  else if !validLeavesInvariant groupId t then
    Result.error "prepare_welcome: invalid leaves"
  else
    pure {
      asInputs := (getLeafList t).map (Option.map leafNodeToAsInput)
    }

end CryptoBytes

/--
Port of `tokens_from_list`.
MLS* requires `List.length tokens == pow2 l`; otherwise, the missing tokens are `none`.
-/
public
def tokensFromList {TokenT: Type}: (l i: Nat) → List (Option TokenT) → ASTokens TokenT l
  | 0, i, tokens => (LeftRightView.leaf (tokens.headD none) i).pack
  | l+1, i, tokens =>
    let (tokensLeft, tokensRight) := tokens.splitAt (2^l)
    (LeftRightView.node () (tokensFromList l i tokensLeft) (tokensFromList l (i + 2^l) tokensRight)).pack

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}

/--
Port of `finalize_welcome`.
MLS* requires `List.Tot.length tokens == pow2 l`; otherwise, see `tokensFromList`.
-/
public
def finalizeWelcome {l: Nat} {t: TreeSync Bytes tkt l} (_pend: PendingWelcome groupId t) (tokens: List (Option TokenT)):
  TreeSyncState Bytes tkt TokenT groupId
:=
  let tokensTree := tokensFromList l t.position tokens
  {
    levels := l
    tree := t
    tokens := tokensTree
  }

/-! ## Add -/

/-- Port of `pending_add`. -/
public
structure PendingAdd (st: TreeSyncState Bytes tkt TokenT groupId) (ln: LeafNode Bytes tkt) where
  asInput: ASInput Bytes

/-- Port of `prepare_add`. -/
public
def prepareAdd (st: TreeSyncState Bytes tkt TokenT groupId) (ln: LeafNode Bytes tkt): Result (PendingAdd st ln) :=
  if !(ln.data.source == .keyPackage) then
    Result.error "prepare_add: source is not key_package"
  else
    match findEmptyLeaf st.tree with
    | some li =>
      if !leafIsValid ln groupId li then
        Result.error "prepare_add: invalid leaf node"
      else
        pure { asInput := leafNodeToAsInput ln }
    | none =>
      let extendedTree := treeExtend st.tree
      match findEmptyLeaf extendedTree with
      | some li =>
        if !leafIsValid ln groupId li then
          Result.error "prepare_add: invalid leaf node"
        else
          pure { asInput := leafNodeToAsInput ln }
      | none => Result.internalFailure "prepare_add: no empty leaf in the extended tree"

/-- Port of `finalize_add`. -/
public
def finalizeAdd {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (_pend: PendingAdd st ln) (token: TokenT): Result (TreeSyncState Bytes tkt TokenT groupId × Nat)
:=
  match findEmptyLeaf st.tree with
  | some li => do
    let newTree ← treeAdd st.tree li ln
    pure (stateUpdateTree st newTree (asAddUpdate st.tokens li token), li)
  | none =>
    let extendedTree := treeExtend st.tree
    let extendedTokens := asExtend st.tokens
    match findEmptyLeaf extendedTree with
    | some li => do
      let newTree ← treeAdd extendedTree li ln
      pure (stateUpdateTree st newTree (asAddUpdate extendedTokens li token), li)
    | none => Result.internalFailure "finalize_add: no empty leaf in the extended tree"

/-! ## Update -/

/-- Port of `pending_update`. -/
public
structure PendingUpdate (st: TreeSyncState Bytes tkt TokenT groupId) (ln: LeafNode Bytes tkt) (li: Nat) where
  asInputBefore: ASInput Bytes
  asInput: ASInput Bytes

/--
Port of `prepare_update`.
MLS* requires `li: treesync_index st` (i.e. `st.tree.containsLeafIndex li`); otherwise, this function fails.
-/
public
def prepareUpdate (st: TreeSyncState Bytes tkt TokenT groupId) (ln: LeafNode Bytes tkt) (li: Nat): Result (PendingUpdate st ln li) :=
  if !(ln.data.source == .update) then
    Result.error "prepare_update: leaf node has invalid source"
  else if !leafIsValid ln groupId li then
    Result.error "prepare_update: leaf node is not valid"
  else if !st.tree.containsLeafIndex li then
    Result.error "prepare_update: leaf index is too big"
  else
    match leafAt st.tree li with
    | none => Result.error "prepare_update: leaf node doesn't exists"
    | some lnBefore =>
      pure {
        asInputBefore := leafNodeToAsInput lnBefore
        asInput := leafNodeToAsInput ln
      }

/-- Port of `finalize_update`. -/
public
def finalizeUpdate {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt} {li: Nat}
  (_pend: PendingUpdate st ln li) (token: TokenT): TreeSyncState Bytes tkt TokenT groupId
:=
  stateUpdateTree st (treeUpdate st.tree li ln) (asAddUpdate st.tokens li token)

/-! ## Remove -/

/-- Port of `pending_remove`. -/
public
structure PendingRemove (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat): Type

/--
Port of `prepare_remove`.
MLS* requires `li: treesync_index st` (i.e. `st.tree.containsLeafIndex li`); otherwise, this function fails.
-/
public
def prepareRemove (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat): Result (PendingRemove st li) :=
  if !st.tree.containsLeafIndex li then
    Result.error "prepare_remove: leaf index is too big"
  else if !(leafAt st.tree li).isSome then
    Result.error "prepare_remove: removed leaf is already blank"
  else
    pure {}

/-- Port of `fully_truncate_state`. -/
public
def fullyTruncateState (st: TreeSyncState Bytes tkt TokenT groupId): TreeSyncState Bytes tkt TokenT groupId :=
  match st with
  | { levels := l+1, tree, tokens } =>
    if isTreeEmpty tree.right then
      fullyTruncateState {
        levels := l
        tree := treeTruncate tree
        tokens := asTruncate tokens
      }
    else
      st
  | st => st
termination_by st.levels

/-- Port of `finalize_remove`. -/
public
def finalizeRemove {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} (_pend: PendingRemove st li):
  TreeSyncState Bytes tkt TokenT groupId
:=
  let blankedTree := treeRemove st.tree li
  let blankedTokens := asRemove st.tokens li
  fullyTruncateState (stateUpdateTree st blankedTree blankedTokens)

/-! ## Commit -/

/-- Port of `pending_commit`. -/
public
structure PendingCommit (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat) (p: PathSync Bytes tkt st.levels) where
  asInputBefore: ASInput Bytes
  asInput: ASInput Bytes

/--
Port of `prepare_commit`.
MLS* requires `li: treesync_index st` (i.e. `st.tree.containsLeafIndex li`); otherwise, this function fails.
-/
public
def prepareCommit (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat) (p: PathSync Bytes tkt st.levels):
  Result (PendingCommit st li p)
:=
  if !pathIsValid groupId st.tree li p then
    Result.error "prepare_commit: invalid path"
  else if !st.tree.containsLeafIndex li then
    Result.error "prepare_commit: leaf index is too big"
  else
    match leafAt st.tree li with
    | none => Result.error "prepare_commit: comitter is blank"
    | some lnBefore =>
      pure {
        asInputBefore := leafNodeToAsInput lnBefore
        asInput := leafNodeToAsInput p.getPathLeaf
      }

/-- Port of `finalize_commit`. -/
public
def finalizeCommit {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} {p: PathSync Bytes tkt st.levels}
  (_pend: PendingCommit st li p) (token: TokenT): Result (TreeSyncState Bytes tkt TokenT groupId)
:= do
  let newTree ← applyPath st.tree li p
  pure (stateUpdateTree st newTree (asAddUpdate st.tokens li token))

/-! ## Weaken -/

/-! ## Authenticate external path -/

/--
Port of `authenticate_external_path`.
MLS* requires `(get_path_leaf p).source == LNS_update`; otherwise, see `externalPathToPath`.
-/
public
def authenticateExternalPath (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat)
  (p: ExternalPathSync Bytes tkt st.levels) (signKey: Bytes) (signNonce: Bytes)
  : Result (PathSync Bytes tkt st.levels)
:=
  externalPathToPath st.tree li p groupId signKey signNonce

/-! ## Compute tree hashes -/

/-- Port of `compute_tree_hash`. -/
@[expose]
public
def computeTreeHash (st: TreeSyncState Bytes tkt TokenT groupId): Result Bytes :=
  treeHash st.tree

/-- Port of `compute_provisional_tree_hash`. -/
public
def computeProvisionalTreeHash (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat) (p: PathSync Bytes tkt st.levels):
  Result Bytes
:= do
  let provisionalTree ← applyPath st.tree li p
  treeHash provisionalTree

end CryptoBytes

end MLS.TreeSync.API
