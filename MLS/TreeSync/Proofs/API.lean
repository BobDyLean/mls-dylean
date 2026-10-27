module

public import MLS.Common.Proofs.TreeCommon
public import MLS.TreeSync.Code.API
public import MLS.TreeSync.Proofs.Invariants.AuthService
public import MLS.TreeSync.Proofs.Invariants.UnmergedLeaves
public import MLS.TreeSync.Proofs.Invariants.ParentHash
public import MLS.TreeSync.Proofs.Invariants.ValidLeaves

/-!
Proofs about `MLS.TreeSync.API`.

MLS*'s API is written with refinement types (the `Refined` interface and the refinements of the `pending_*` types),
and proves the authentication service invariant in `_valid` lemmas. Here:
- the refinements of the `pending_*` types are the predicates `Pending*.Valid`,
  established by the `prepare_*` functions (`prepare*_valid`);
- the refinement `treesync_valid` on the tree of the state is `TreeSyncState.TreeValid`,
  preserved by the `finalize_*` functions (`finalize*_treeValid`), as the pre / post-conditions of MLS*'s API;
- the `_valid` lemmas of MLS* are ported as is (about `treesyncStateValid`).
-/

namespace MLS.TreeSync.API

open Comparse
open MLS MLS.TreeSync

/-! ## Tokens from a list -/

@[simp]
theorem tokensFromList_position {TokenT: Type} (l i: Nat) (tokens: List (Option TokenT)):
  (tokensFromList l i tokens).position = i
:= by
  induction l generalizing i tokens <;> simp_all [tokensFromList]

/-- Port of `leaf_at_token_from_list`. -/
theorem leafAt_tokensFromList {TokenT: Type} (l i: Nat) (tokens: List (Option TokenT)) (li: Nat)
  (hlen: tokens.length = 2^l) (hli: i ≤ li ∧ li < i + 2^l):
  some (leafAt (tokensFromList l i tokens) li) = tokens[li - i]?
:= by
  induction l generalizing i tokens with
  | zero =>
    match tokens with
    | [token] => grind [tokensFromList, leafAt.eq_def]
  | succ l ih =>
    rw [leafAt.eq_def]
    simp only [tokensFromList]
    grind [tokensFromList_position]

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}

/-! ## Predicates -/

/--
MLS*'s refinement `treesync_valid` (from `MLS.TreeSync.Refined.Types`) on the tree of the state:
the tree satisfies all the TreeSync invariants.
-/
@[expose]
public
def _root_.MLS.TreeSync.TreeSyncState.TreeValid (st: TreeSyncState Bytes tkt TokenT groupId): Prop :=
  unmergedLeavesOk st.tree ∧ parentHashInvariant st.tree ∧ validLeavesInvariant groupId st.tree

/-- MLS*'s refinements of `pending_create`: `pending_create_proof` and `as_input: as_input_for ln`. -/
@[expose]
public
def PendingCreate.Valid {ln: LeafNode Bytes tkt} (pend: PendingCreate groupId ln): Prop :=
  leafIsValid ln groupId 0 ∧
  pend.asInput = leafNodeToAsInput ln

/-- MLS*'s refinements of `pending_welcome`: `pending_welcome_proof` and `as_inputs_proof`. -/
@[expose]
public
def PendingWelcome.Valid {l: Nat} {t: TreeSync Bytes tkt l} (pend: PendingWelcome groupId t): Prop :=
  (unmergedLeavesOk t ∧ parentHashInvariant t ∧ validLeavesInvariant groupId t) ∧
  pend.asInputs.length = 2^l ∧
  ∀ li, t.containsLeafIndex li → pend.asInputs[li - t.position]? = some ((leafAt t li).map leafNodeToAsInput)

/-- MLS*'s refinements of `pending_add`: `pending_add_proof` and `as_input: as_input_for ln`. -/
@[expose]
public
def PendingAdd.Valid {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt} (pend: PendingAdd st ln): Prop :=
  (ln.data.source = .keyPackage ∧
    match findEmptyLeaf st.tree with
    | some li => leafIsValid ln groupId li
    | none =>
      match findEmptyLeaf (treeExtend st.tree) with
      | some li => leafIsValid ln groupId li
      | none => True) ∧
  pend.asInput = leafNodeToAsInput ln

/--
MLS*'s refinements of `pending_update`: `pending_update_proof`
(with `li: treesync_index st`, i.e. `st.tree.containsLeafIndex li`),
`as_input_before: as_input_for (state_leaf_at st li)` and `as_input: as_input_for ln`.
-/
@[expose]
public
def PendingUpdate.Valid {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt} {li: Nat}
  (pend: PendingUpdate st ln li): Prop
:=
  (ln.data.source = .update ∧ leafIsValid ln groupId li ∧ st.tree.containsLeafIndex li ∧ (leafAt st.tree li).isSome) ∧
  (leafAt st.tree li).map leafNodeToAsInput = some pend.asInputBefore ∧
  pend.asInput = leafNodeToAsInput ln

/--
MLS*'s refinement of `pending_remove`: `pending_remove_proof`
(with `li: treesync_index st`, i.e. `st.tree.containsLeafIndex li`).
-/
@[expose]
public
def PendingRemove.Valid {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} (_pend: PendingRemove st li): Prop :=
  st.tree.containsLeafIndex li ∧ (leafAt st.tree li).isSome

/--
MLS*'s refinements of `pending_commit`: `pending_commit_proof`
(with `li: treesync_index st`, i.e. `st.tree.containsLeafIndex li`),
`as_input_before: as_input_for (state_leaf_at st li)` and `as_input: as_input_for (get_path_leaf p)`.
-/
@[expose]
public
def PendingCommit.Valid {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} {p: PathSync Bytes tkt st.levels}
  (pend: PendingCommit st li p): Prop
:=
  (pathIsValid groupId st.tree li p ∧ st.tree.containsLeafIndex li ∧ (leafAt st.tree li).isSome) ∧
  (leafAt st.tree li).map leafNodeToAsInput = some pend.asInputBefore ∧
  pend.asInput = leafNodeToAsInput p.getPathLeaf

/-! ## The `prepare_*` functions establish the refinements of the pending states -/

public
theorem prepareCreate_valid (ln: LeafNode Bytes tkt) (pend: PendingCreate groupId ln)
  (h: prepareCreate groupId ln = .success pend):
  pend.Valid
:= by
  unfold prepareCreate at h
  split at h <;> simp_all [PendingCreate.Valid, Result.error] <;> grind

public
theorem prepareWelcome_valid {l: Nat} (t: TreeSync Bytes tkt l) (pend: PendingWelcome groupId t)
  (h: prepareWelcome groupId t = .success pend):
  pend.Valid
:= by
  unfold prepareWelcome at h
  repeat (split at h; · simp [Result.error] at h)
  cases h
  refine ⟨by simp_all, by simp [length_getLeafList], ?_⟩
  intro li hli
  have := index_getLeafList t (li - t.position) (by grind [Tree.containsLeafIndex])
  grind [Tree.containsLeafIndex]

public
theorem prepareAdd_valid (st: TreeSyncState Bytes tkt TokenT groupId) (ln: LeafNode Bytes tkt) (pend: PendingAdd st ln)
  (h: prepareAdd st ln = .success pend):
  pend.Valid
:= by
  unfold prepareAdd at h
  split at h
  · simp [Result.error] at h
  · simp only [PendingAdd.Valid]
    split at h
    · split at h <;> simp_all [Result.error]; grind
    · dsimp only at h
      split at h
      · split at h <;> simp_all [Result.error]; grind
      · simp [Result.internalFailure] at h

public
theorem prepareUpdate_valid (st: TreeSyncState Bytes tkt TokenT groupId) (ln: LeafNode Bytes tkt) (li: Nat)
  (pend: PendingUpdate st ln li) (h: prepareUpdate st ln li = .success pend):
  pend.Valid
:= by
  unfold prepareUpdate at h
  repeat (split at h; · simp [Result.error] at h)
  cases h
  simp_all [PendingUpdate.Valid]

public
theorem prepareRemove_valid (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat)
  (pend: PendingRemove st li) (h: prepareRemove st li = .success pend):
  pend.Valid
:= by
  unfold prepareRemove at h
  repeat (split at h; · simp [Result.error] at h)
  simp_all [PendingRemove.Valid, Option.isSome_iff_ne_none]

public
theorem prepareCommit_valid (st: TreeSyncState Bytes tkt TokenT groupId) (li: Nat) (p: PathSync Bytes tkt st.levels)
  (pend: PendingCommit st li p) (h: prepareCommit st li p = .success pend):
  pend.Valid
:= by
  unfold prepareCommit at h
  repeat (split at h; · simp [Result.error] at h)
  cases h
  simp_all [PendingCommit.Valid]

/-! ## Unfolding the `finalize_*` functions -/

/-- The result of a successful `finalizeAdd`: the leaf is added in the first empty leaf, possibly after extending the tree. -/
public
theorem finalizeAdd_success {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (pend: PendingAdd st ln) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId) (li: Nat)
  (h: finalizeAdd pend token = .success (res, li)):
  (findEmptyLeaf st.tree = some li ∧ ∃ newTree, treeAdd st.tree li ln = .success newTree ∧
    res = stateUpdateTree st newTree (asAddUpdate st.tokens li token)) ∨
  (findEmptyLeaf st.tree = none ∧ findEmptyLeaf (treeExtend st.tree) = some li ∧ ∃ newTree, treeAdd (treeExtend st.tree) li ln = .success newTree ∧
    res = stateUpdateTree st newTree (asAddUpdate (asExtend st.tokens) li token))
:= by
  unfold finalizeAdd at h
  split at h
  · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
    grind
  · dsimp only at h
    split at h
    · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
      grind
    · simp [Result.internalFailure] at h

/-- The result of a successful `finalizeCommit`. -/
public
theorem finalizeCommit_success {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} {p: PathSync Bytes tkt st.levels}
  (pend: PendingCommit st li p) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId)
  (h: finalizeCommit pend token = .success res):
  ∃ newTree, applyPath st.tree li p = .success newTree ∧ res = stateUpdateTree st newTree (asAddUpdate st.tokens li token)
:= by
  simp only [finalizeCommit, Result.bind_eq_success, Result.pure_eq_success] at h
  grind

/-- A property preserved by each truncation step (of a tree whose right subtree is empty) is preserved by `fullyTruncateState`. -/
public
theorem fullyTruncateState_preserves (P: TreeSyncState Bytes tkt TokenT groupId → Prop)
  (hstep: ∀ {l: Nat} (tree: TreeSync Bytes tkt (l+1)) (tokens: ASTokens TokenT (l+1)), isTreeEmpty tree.right →
    P { levels := l+1, tree, tokens } → P { levels := l, tree := treeTruncate tree, tokens := asTruncate tokens })
  (st: TreeSyncState Bytes tkt TokenT groupId) (h: P st):
  P (fullyTruncateState st)
:= by
  match st with
  | { levels := l+1, tree, tokens } =>
    rw [fullyTruncateState]
    split
    · exact fullyTruncateState_preserves P hstep _ (hstep tree tokens (by assumption) h)
    · exact h
  | { levels := 0, tree, tokens } =>
    simpa [fullyTruncateState] using h
termination_by st.levels

/-! ## The `finalize_*` functions preserve the TreeSync invariants -/

public
theorem finalizeCreate_treeValid {ln: LeafNode Bytes tkt} (pend: PendingCreate groupId ln) (token: TokenT)
  (hpend: pend.Valid):
  (finalizeCreate pend token).TreeValid
:= by
  grind [TreeSyncState.TreeValid, PendingCreate.Valid, finalizeCreate,
    unmergedLeavesOk_treeCreate, parentHashInvariant_treeCreate, validLeavesInvariant_treeCreate]

public
theorem finalizeWelcome_treeValid {l: Nat} {t: TreeSync Bytes tkt l} (pend: PendingWelcome groupId t) (tokens: List (Option TokenT))
  (hpend: pend.Valid):
  (finalizeWelcome pend tokens).TreeValid
:=
  hpend.1

/-- The TreeSync invariants are preserved by adding a leaf in an empty leaf of the tree (`finalizeAdd`). -/
theorem treeValid_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (ln: LeafNode Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: treeAdd t li ln = .success t') (hli: findEmptyLeaf t = some li) (hln: leafIsValid ln groupId li)
  (hinv: unmergedLeavesOk t ∧ parentHashInvariant t ∧ validLeavesInvariant groupId t):
  unmergedLeavesOk t' ∧ parentHashInvariant t' ∧ validLeavesInvariant groupId t'
:= by
  have := findEmptyLeaf_spec t li hli
  grind [unmergedLeavesOk_treeAdd, parentHashInvariant_treeAdd, validLeavesInvariant_treeAdd]

public
theorem finalizeAdd_treeValid {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (pend: PendingAdd st ln) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId) (li: Nat)
  (h: finalizeAdd pend token = .success (res, li))
  (hpend: pend.Valid) (hst: st.TreeValid):
  res.TreeValid
:= by
  have hcan := hpend.1.2
  rcases finalizeAdd_success pend token res li h with ⟨heq, newTree, h1, rfl⟩ | ⟨heq, heq', newTree, h1, rfl⟩
  · simp only [heq] at hcan
    grind [treeValid_treeAdd, TreeSyncState.TreeValid, stateUpdateTree]
  · simp only [heq'] at hcan
    grind [treeValid_treeAdd, TreeSyncState.TreeValid, stateUpdateTree,
      unmergedLeavesOk_treeExtend, parentHashInvariant_treeExtend, validLeavesInvariant_treeExtend]

public
theorem finalizeUpdate_treeValid {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt} {li: Nat}
  (pend: PendingUpdate st ln li) (token: TokenT)
  (hpend: pend.Valid) (hst: st.TreeValid):
  (finalizeUpdate pend token).TreeValid
:= by
  grind [TreeSyncState.TreeValid, PendingUpdate.Valid, finalizeUpdate, stateUpdateTree,
    unmergedLeavesOk_treeUpdate, parentHashInvariant_treeUpdate, validLeavesInvariant_treeUpdate]

public
theorem fullyTruncateState_treeValid (st: TreeSyncState Bytes tkt TokenT groupId) (hst: st.TreeValid):
  (fullyTruncateState st).TreeValid
:= by
  apply fullyTruncateState_preserves _ _ st hst
  grind [TreeSyncState.TreeValid,
    unmergedLeavesOk_treeTruncate, parentHashInvariant_treeTruncate, validLeavesInvariant_treeTruncate]

public
theorem finalizeRemove_treeValid {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat}
  (pend: PendingRemove st li) (hpend: pend.Valid) (hst: st.TreeValid):
  (finalizeRemove pend).TreeValid
:= by
  apply fullyTruncateState_treeValid
  grind [TreeSyncState.TreeValid, PendingRemove.Valid, stateUpdateTree,
    unmergedLeavesOk_treeRemove, parentHashInvariant_treeRemove, validLeavesInvariant_treeRemove]

public
theorem finalizeCommit_treeValid {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat} {p: PathSync Bytes tkt st.levels}
  (pend: PendingCommit st li p) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId)
  (h: finalizeCommit pend token = .success res)
  (hpend: pend.Valid) (hst: st.TreeValid):
  res.TreeValid
:= by
  obtain ⟨newTree, h1, rfl⟩ := finalizeCommit_success pend token res h
  grind [TreeSyncState.TreeValid, PendingCommit.Valid, stateUpdateTree, pathIsValid, pathLeafIsValid,
    unmergedLeavesOk_applyPath, parentHashInvariant_applyPath, validLeavesInvariant_applyPath]

/-! ## Authentication service invariant (MLS*'s `_valid` lemmas) -/

/-- Port of `finalize_create_valid`. -/
public
theorem finalizeCreate_valid {asp: ASParameters Bytes TokenT} {ln: LeafNode Bytes tkt}
  (pend: PendingCreate groupId ln) (token: TokenT)
  (hpend: pend.Valid) (h: asp.credentialOk pend.asInput token):
  treesyncStateValid asp (finalizeCreate pend token)
:= by
  grind [treesyncStateValid, finalizeCreate, PendingCreate.Valid, allCredentialsOk_treeCreate, leafNodeToAsInput, treeCreate]

/--
The precondition of MLS*'s `finalize_welcome_valid`: each token is valid for the AS input of its leaf
(the tokens of blank leaves are `none`).
-/
@[expose]
public
def TokensForAsInputs (asp: ASParameters Bytes TokenT) (asInputs: List (Option (ASInput Bytes)))
  (tokens: List (Option TokenT)): Prop :=
  ∀ li < tokens.length, match asInputs[li]?, tokens[li]? with
    | some (some asInp), some (some token) => asp.credentialOk asInp token
    | some none, some none => True
    | _, _ => False

/--
Port of `finalize_welcome_valid`.
MLS* requires `List.Tot.length tokens == pow2 l` (here `hlen`).
-/
public
theorem finalizeWelcome_valid {asp: ASParameters Bytes TokenT} {l: Nat} {t: TreeSync Bytes tkt l}
  (pend: PendingWelcome groupId t) (tokens: List (Option TokenT))
  (hpend: pend.Valid) (hlen: tokens.length = 2^l) (h: TokensForAsInputs asp pend.asInputs tokens):
  treesyncStateValid asp (finalizeWelcome pend tokens)
:= by
  refine ⟨by simp [finalizeWelcome], ?_⟩
  apply allCredentialsOk_intro
  · simp [finalizeWelcome]
  · intro li hli
    have hli': t.containsLeafIndex li := hli
    have h1 := hpend.2.2 li hli'
    have h2 := leafAt_tokensFromList l t.position tokens li hlen (by grind [Tree.containsLeafIndex])
    have h3 := h (li - t.position) (by grind [Tree.containsLeafIndex])
    rw [h1, ← h2] at h3
    simp only [finalizeWelcome, oneCredentialOk]
    revert h3
    cases leafAt t li <;> cases leafAt (tokensFromList l t.position tokens) li <;> simp [Option.map]

/-- Port of `finalize_add_valid`. -/
public
theorem finalizeAdd_valid {asp: ASParameters Bytes TokenT} {st: TreeSyncState Bytes tkt TokenT groupId} {ln: LeafNode Bytes tkt}
  (pend: PendingAdd st ln) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId) (li: Nat)
  (h: finalizeAdd pend token = .success (res, li))
  (hpend: pend.Valid) (hcred: asp.credentialOk pend.asInput token) (hvalid: treesyncStateValid asp st):
  treesyncStateValid asp res
:= by
  rcases finalizeAdd_success pend token res li h with ⟨heq, newTree, h1, rfl⟩ | ⟨-, heq, newTree, h1, rfl⟩ <;>
    have := findEmptyLeaf_spec _ _ heq
  all_goals grind [treesyncStateValid, PendingAdd.Valid, stateUpdateTree, asAddUpdate, treeExtend, asExtend,
    allCredentialsOk_treeExtend, allCredentialsOk_treeAdd, leafNodeToAsInput]

/-- Port of `finalize_update_valid`. -/
public
theorem finalizeUpdate_valid {asp: ASParameters Bytes TokenT} {st: TreeSyncState Bytes tkt TokenT groupId}
  {ln: LeafNode Bytes tkt} {li: Nat}
  (pend: PendingUpdate st ln li) (token: TokenT)
  (hpend: pend.Valid) (hcred: asp.credentialOk pend.asInput token) (hvalid: treesyncStateValid asp st):
  treesyncStateValid asp (finalizeUpdate pend token)
:= by
  grind [treesyncStateValid, PendingUpdate.Valid, finalizeUpdate, stateUpdateTree, treeUpdate, asAddUpdate,
    allCredentialsOk_treeUpdate, leafNodeToAsInput]

/-- Port of `fully_truncate_state_valid`. -/
public
theorem fullyTruncateState_valid {asp: ASParameters Bytes TokenT} (st: TreeSyncState Bytes tkt TokenT groupId)
  (hvalid: treesyncStateValid asp st):
  treesyncStateValid asp (fullyTruncateState st)
:= by
  apply fullyTruncateState_preserves _ _ st hvalid
  grind [treesyncStateValid, treeTruncate, asTruncate, allCredentialsOk_treeTruncate]

/-- Port of `finalize_remove_valid`. -/
public
theorem finalizeRemove_valid {asp: ASParameters Bytes TokenT} {st: TreeSyncState Bytes tkt TokenT groupId} {li: Nat}
  (pend: PendingRemove st li) (hpend: pend.Valid) (hvalid: treesyncStateValid asp st):
  treesyncStateValid asp (finalizeRemove pend)
:= by
  apply fullyTruncateState_valid
  grind [treesyncStateValid, PendingRemove.Valid, stateUpdateTree, treeRemove, asRemove, allCredentialsOk_treeRemove]

/-- Port of `finalize_commit_valid`. -/
public
theorem finalizeCommit_valid {asp: ASParameters Bytes TokenT} {st: TreeSyncState Bytes tkt TokenT groupId}
  {li: Nat} {p: PathSync Bytes tkt st.levels}
  (pend: PendingCommit st li p) (token: TokenT) (res: TreeSyncState Bytes tkt TokenT groupId)
  (h: finalizeCommit pend token = .success res)
  (hpend: pend.Valid) (hcred: asp.credentialOk pend.asInput token) (hvalid: treesyncStateValid asp st):
  treesyncStateValid asp res
:= by
  obtain ⟨newTree, h1, rfl⟩ := finalizeCommit_success pend token res h
  grind [treesyncStateValid, PendingCommit.Valid, applyPath, stateUpdateTree, asAddUpdate, allCredentialsOk_applyPath, leafNodeToAsInput]

/--
Port of `weaken_asp`.
MLS*'s hypothesis `asp_strong.token_t == token_t` holds by typing.
-/
public
theorem weakenAsp (aspStrong aspWeak: ASParameters Bytes TokenT) (st: TreeSyncState Bytes tkt TokenT groupId)
  (hweak: asParametersWeaker aspStrong aspWeak) (hvalid: treesyncStateValid aspStrong st):
  treesyncStateValid aspWeak st
:= by
  grind [treesyncStateValid, allCredentialsOk_weaken]

end CryptoBytes

end MLS.TreeSync.API
