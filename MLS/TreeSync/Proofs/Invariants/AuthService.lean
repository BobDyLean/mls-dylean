import MLS.TreeSync.Code.Invariants.AuthService
import MLS.TreeSync.Proofs.Operations

/-!
Port of `MLS.TreeSync.Invariants.AuthService.Proofs`.

Port-specific differences:
- The positions of the TreeSync tree and of the tokens are equal by hypothesis (`hpos`),
  see `MLS.TreeSync.Invariants.AuthService`.
- `intro_all_credentials_ok` and `elim_all_credentials_ok` are stated with `t.containsLeafIndex li`
  (MLS*'s `li: leaf_index l i`).
- `allCredentialsOk_changeLeaf` factors the proofs for `treeAdd`, `treeUpdate`, `treeRemove` and `applyPath`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {asp: ASParameters Bytes TokenT}

/-! ## Unfolding lemmas -/

theorem oneCredentialOk_succ {l: Nat} (ts: TreeSync Bytes tkt (l+1)) (ast: ASTokens TokenT (l+1)) (li: Nat):
  oneCredentialOk asp ts ast li = oneCredentialOk asp (ts.child li) (ast.child li) li
:= by
  simp only [oneCredentialOk]
  rw [leafAt.eq_def ts, leafAt.eq_def ast]
  simp

theorem allCredentialsOk_zero (ts: TreeSync Bytes tkt 0) (ast: ASTokens TokenT 0) (li: Nat):
  allCredentialsOk asp ts ast ↔ oneCredentialOk asp ts ast li
:= by
  obtain ⟨_, bt⟩ := ts
  obtain ⟨_, bt'⟩ := ast
  cases bt with | leaf c =>
  cases bt' with | leaf c' =>
  rw [allCredentialsOk.eq_def]
  cases c <;> cases c' <;> simp [oneCredentialOk, leafAt.eq_def] <;> rfl

theorem allCredentialsOk_left_right {l: Nat} (ts: TreeSync Bytes tkt (l+1)) (ast: ASTokens TokenT (l+1)):
  allCredentialsOk asp ts ast ↔ allCredentialsOk asp ts.left ast.left ∧ allCredentialsOk asp ts.right ast.right
:= by
  rw [allCredentialsOk.eq_def]
  simp

theorem allCredentialsOk_succ {l: Nat} (ts: TreeSync Bytes tkt (l+1)) (ast: ASTokens TokenT (l+1)) (li: Nat)
  (hpos: ts.position = ast.position):
  allCredentialsOk asp ts ast ↔ allCredentialsOk asp (ts.child li) (ast.child li) ∧ allCredentialsOk asp (ts.sibling li) (ast.sibling li)
:= by
  grind [allCredentialsOk_left_right]

/-- Port of `intro_all_credentials_ok`. -/
theorem allCredentialsOk_intro {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l)
  (hpos: ts.position = ast.position) (h: ∀ li, ts.containsLeafIndex li → oneCredentialOk asp ts ast li):
  allCredentialsOk asp ts ast
:= by
  induction ts using Tree.leftRightInduction with
  | leaf ts => grind [allCredentialsOk_zero ts ast ts.position, Tree.containsLeafIndex_position]
  | node ts ihl ihr =>
    rw [allCredentialsOk_left_right]
    refine ⟨ihl ast.left (by grind) ?_, ihr ast.right (by grind) ?_⟩ <;>
    · intro li hli
      have := h li (by grind [Tree.containsLeafIndex])
      grind [oneCredentialOk_succ, Tree.containsLeafIndex]

/-- Port of `elim_all_credentials_ok`. -/
theorem allCredentialsOk_elim {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l) (li: Nat)
  (hpos: ts.position = ast.position) (h: allCredentialsOk asp ts ast):
  oneCredentialOk asp ts ast li
:= by
  induction ts using Tree.childInduction li with
  | leaf ts => grind [allCredentialsOk_zero ts ast li]
  | node ts ih =>
    rw [oneCredentialOk_succ]
    apply ih <;> grind [allCredentialsOk_succ ts ast li hpos]

/-! ## Invariant theorems -/

/-- Port of `all_credentials_ok_tree_create`. -/
theorem allCredentialsOk_treeCreate (ln: LeafNode Bytes tkt) (token: TokenT)
  (h: asp.credentialOk (ln.data.signatureKey, ln.data.credential) token):
  allCredentialsOk asp (treeCreate ln: TreeSync Bytes tkt 0) (treeCreate token: ASTokens TokenT 0)
:= by
  rw [allCredentialsOk_zero _ _ 0]
  simp_all [oneCredentialOk, leafAt.eq_def, treeCreate, leafNodeToAsInput]

/--
The invariant is preserved when the tree and the tokens only change at the leaf `li`,
with a new leaf `oln` and a new token `otoken` that satisfy it.
Factors the proofs of MLS*'s `all_credentials_ok_tree_add`, `_tree_update`, `_tree_remove` and `_apply_path`
(each of them is `intro_all_credentials_ok` with `elim_all_credentials_ok` and two `leaf_at` lemmas).
-/
theorem allCredentialsOk_changeLeaf {l: Nat} (ts ts': TreeSync Bytes tkt l) (ast ast': ASTokens TokenT l) (li: Nat)
  (oln: Option (LeafNode Bytes tkt)) (otoken: Option TokenT)
  (hpos: ts.position = ast.position) (hpos': ts'.position = ts.position) (hposa': ast'.position = ast.position)
  (hnew: match oln, otoken with
    | some ln, some token => asp.credentialOk (leafNodeToAsInput ln) token
    | none, none => True
    | _, _ => False)
  (hts': ∀ li', ts.containsLeafIndex li' → leafAt ts' li' = if li = li' then oln else leafAt ts li')
  (hast': ∀ li', ast.containsLeafIndex li' → leafAt ast' li' = if li = li' then otoken else leafAt ast li')
  (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp ts' ast'
:= by
  apply allCredentialsOk_intro
  · grind
  · intro li' hli'
    have := allCredentialsOk_elim ts ast li' hpos hinv
    have := Tree.containsLeafIndex_of_position_eq ts ast li' hpos (by grind [Tree.containsLeafIndex])
    unfold oneCredentialOk at *
    rw [hts' li' (by grind [Tree.containsLeafIndex]), hast' li' (by assumption)]
    grind

/--
Port of `all_credentials_ok_tree_add`.
MLS* requires `li: leaf_index l i` (here `hli`).
-/
theorem allCredentialsOk_treeAdd {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l) (li: Nat)
  (ln: LeafNode Bytes tkt) (token: TokenT) (ts': TreeSync Bytes tkt l) (h: treeAdd ts li ln = .success ts')
  (hpos: ts.position = ast.position) (hli: ts.containsLeafIndex li)
  (hcred: asp.credentialOk (ln.data.signatureKey, ln.data.credential) token) (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp ts' (asAddUpdate ast li token)
:= by
  have := Tree.containsLeafIndex_of_position_eq ts ast li hpos hli
  apply allCredentialsOk_changeLeaf ts ts' ast _ li (some ln) (some token)
  case hts' => exact fun li' hli' => leafAt_treeAdd ts li ln li' ts' h hli hli'
  all_goals grind [treeAdd_position, asAddUpdate, leafAt_treeChangePath, leafNodeToAsInput]

/--
Port of `all_credentials_ok_tree_update`.
MLS* requires `li: leaf_index l i` (here `hli`).
-/
theorem allCredentialsOk_treeUpdate {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l) (li: Nat)
  (ln: LeafNode Bytes tkt) (token: TokenT)
  (hpos: ts.position = ast.position) (hli: ts.containsLeafIndex li)
  (hcred: asp.credentialOk (ln.data.signatureKey, ln.data.credential) token) (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp (treeUpdate ts li ln) (asAddUpdate ast li token)
:= by
  have := Tree.containsLeafIndex_of_position_eq ts ast li hpos hli
  apply allCredentialsOk_changeLeaf ts _ ast _ li (some ln) (some token) <;>
    grind [treeUpdate, asAddUpdate, leafAt_treeChangePath, leafNodeToAsInput]

/--
Port of `all_credentials_ok_tree_remove`.
MLS* requires `li: leaf_index l i` (here `hli`).
-/
theorem allCredentialsOk_treeRemove {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l) (li: Nat)
  (hpos: ts.position = ast.position) (hli: ts.containsLeafIndex li) (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp (treeRemove ts li) (asRemove ast li)
:= by
  have := Tree.containsLeafIndex_of_position_eq ts ast li hpos hli
  apply allCredentialsOk_changeLeaf ts _ ast _ li none none <;>
    grind [treeRemove, asRemove, leafAt_treeChangePath]

/--
Port of `all_credentials_ok_left_right`.
It is the forward direction of `allCredentialsOk_left_right`.
-/
theorem allCredentialsOk_left_right_of {l: Nat} (ts: TreeSync Bytes tkt (l+1)) (ast: ASTokens TokenT (l+1))
  (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp ts.left ast.left ∧ allCredentialsOk asp ts.right ast.right
:=
  (allCredentialsOk_left_right ts ast).mp hinv

/--
Port of `all_credentials_ok_tree_truncate`.
MLS* requires `is_tree_empty (TNode?.right ts)`; this hypothesis is not needed here.
-/
theorem allCredentialsOk_treeTruncate {l: Nat} (ts: TreeSync Bytes tkt (l+1)) (ast: ASTokens TokenT (l+1))
  (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp (treeTruncate ts) (asTruncate ast)
:=
  (allCredentialsOk_left_right_of ts ast hinv).1

theorem allCredentialsOk_mkBlankTreeGeneral (l p p': Nat):
  allCredentialsOk asp (mkBlankTreeGeneral l p none none: TreeSync Bytes tkt l) (mkBlankTreeGeneral l p' none (): ASTokens TokenT l)
:= by
  induction l generalizing p p' with
  | zero => simp [allCredentialsOk_zero _ _ 0, oneCredentialOk, leafAt.eq_def, mkBlankTreeGeneral]
  | succ l ih => simp_all [allCredentialsOk_left_right, mkBlankTreeGeneral]

/--
Port of `all_credentials_ok_tree_extend`.
Unlike MLS*, the proof does not go through `intro_all_credentials_ok`:
the new right subtrees are blank (`allCredentialsOk_mkBlankTreeGeneral`).
-/
theorem allCredentialsOk_treeExtend {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l)
  (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp (treeExtend ts) (asExtend ast)
:= by
  simp [allCredentialsOk_left_right, treeExtend, asExtend, hinv, allCredentialsOk_mkBlankTreeGeneral, mkBlankTree]

/-! ## Weakening theorem -/

/-- Port of `as_parameters_weaker`. -/
def asParametersWeaker (asStrong asWeak: ASParameters Bytes TokenT): Prop :=
  ∀ vk cred token, asStrong.credentialOk (vk, cred) token → asWeak.credentialOk (vk, cred) token

/-- Port of `all_credentials_ok_weaken`. -/
theorem allCredentialsOk_weaken {aspStrong: ASParameters Bytes TokenT} {l: Nat}
  (aspWeak: ASParameters Bytes TokenT) (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l)
  (hweak: asParametersWeaker aspStrong aspWeak) (hinv: allCredentialsOk aspStrong ts ast):
  allCredentialsOk aspWeak ts ast
:= by
  induction ts using Tree.leftRightInduction with
  | leaf ts =>
    rw [allCredentialsOk_zero _ _ 0] at hinv ⊢
    unfold oneCredentialOk at *
    split <;> simp_all [leafNodeToAsInput, asParametersWeaker]
  | node ts ihl ihr =>
    grind [allCredentialsOk_left_right]

end MLS.TreeSync

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {asp: ASParameters Bytes TokenT}

/--
Port of `all_credentials_ok_apply_path`.
MLS* requires `li: leaf_index l 0` (here `hli`).
-/
theorem allCredentialsOk_applyPath {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l) (li: Nat)
  (p: PathSync Bytes tkt l) (token: TokenT) (ts': TreeSync Bytes tkt l) (h: applyPath ts li p = .success ts')
  (hpos: ts.position = ast.position) (hli: ts.containsLeafIndex li)
  (hcred: asp.credentialOk (p.getPathLeaf.data.signatureKey, p.getPathLeaf.data.credential) token)
  (hinv: allCredentialsOk asp ts ast):
  allCredentialsOk asp ts' (asAddUpdate ast li token)
:= by
  have := Tree.containsLeafIndex_of_position_eq ts ast li hpos hli
  apply allCredentialsOk_changeLeaf ts ts' ast _ li (some p.getPathLeaf) (some token)
  case hts' => exact fun li' hli' => leafAt_applyPathAux ts li p _ li' ts' h hli hli'
  case hpos' => exact applyPathAux_position ts li p _ ts' h
  all_goals grind [asAddUpdate, leafAt_treeChangePath, leafNodeToAsInput]

end MLS.TreeSync
