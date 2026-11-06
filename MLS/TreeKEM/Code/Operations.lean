module

public import MLS.Common.Code.TreeCommon
public import MLS.Common.Code.Crypto.Derived
public import MLS.TreeKEM.Code.Types

/-!
Port of `MLS.TreeKEM.Operations`.

Port-specific differences:
- Functions recurse on the views of `MLS.Tree`: `ChildSiblingView` for functions following a leaf index,
  `LeftRightView` for functions visiting both children.
- Leaf indices are plain `Nat`s (see `MLS.Tree`).
- Paths are not indexed by the position of the tree and the leaf index (see `MLS.Path`):
  functions recursing on a tree and a path take the leaf index as an explicit argument,
  functions recursing on a path alone in MLS* (`path_blank`, `get_path_secret_of_added_leaf`,
  `compute_least_common_ancestor_level`) also take the tree of the path, and recurse on its child / sibling view.
- Preconditions of MLS* (e.g. `treekem_invariant t`) are not ported:
  functions fail or have a default behavior when they are not met (see the docstrings).
- `find_index` is `List.idxOf?`.
- `path_secret_level l` (`x:nat{0 < x /\ x <= l}`) is `Nat`.
-/

namespace MLS.TreeKEM

open Comparse
open MLS

section Tree

variable {Bytes: Type}

/--
Port of `tree_add`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def treeAdd {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (lp: TreeKEMLeaf Bytes): TreeKEM Bytes l :=
  match t.intoChildSiblingView li with
  | .leaf _ position => (ChildSiblingView.leaf (some lp) position).pack
  | .node optContent child sibling =>
    let newOptContent := optContent.map fun content =>
      { content with unmergedLeaves := insertSorted li content.unmergedLeaves }
    (ChildSiblingView.node newOptContent (treeAdd child li lp) sibling).pack
termination_by l

/--
Port of `tree_apply_path`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def treeApplyPath [BytesLike Bytes] {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathKEM Bytes l): TreeKEM Bytes l :=
  match t.intoChildSiblingView li, p with
  | .leaf _ position, .leaf mi => (ChildSiblingView.leaf (some mi) position).pack
  | .node _ child sibling, .node oupn pNext =>
    let newOptContent := oupn.map fun upn =>
      { publicKey := upn.encryptionKey.val, unmergedLeaves := [] }
    (ChildSiblingView.node newOptContent (treeApplyPath child li pNext) sibling).pack
termination_by l

/--
Port of `path_blank`.
Unlike MLS*, this function takes the tree `t` of the path, and follows the path with its child / sibling view.
MLS* requires `blank_li <> li`; otherwise, the private key of the leaf is kept.
MLS* requires `blank_li: leaf_index l i` (i.e. `t.containsLeafIndex blankLi`); otherwise, only the root is blanked.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def pathBlank {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: TreeKEMPriv Bytes l) (blankLi: Nat): TreeKEMPriv Bytes l :=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf sk => .leaf sk
  | .node _ child _, .node _ pNext =>
    if child.containsLeafIndex blankLi then
      .node none (pathBlank child li pNext blankLi)
    else
      .node none pNext
termination_by l

/-- Port of `path_extend`. -/
public
def pathExtend {l: Nat} (p: TreeKEMPriv Bytes l): TreeKEMPriv Bytes (l+1) :=
  .node none p

/-- Port of `path_truncate`. -/
public
def pathTruncate {l: Nat} (p: TreeKEMPriv Bytes (l+1)): TreeKEMPriv Bytes l :=
  match p with
  | .node _ pNext => pNext

end Tree

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `derive_keypair_from_path_secret`. -/
public
def deriveKeypairFromPathSecret (pathSecret: Bytes): Result (Bytes × Bytes) := do
  let nodeSecret ← deriveSecret pathSecret "node"
  CryptoBytes.hpkeGenKeypair nodeSecret

/-- Port of `derive_next_path_secret`. -/
public
def deriveNextPathSecret (pathSecret: Bytes): Result Bytes :=
  deriveSecret pathSecret "path"

/-- Port of `un_addP`. -/
public
def unAddP {l: Nat} (t: TreeKEM Bytes l) (pred: Nat → Bool): TreeKEM Bytes l :=
  match t.intoLeftRightView with
  | .leaf content position => (LeftRightView.leaf (if pred position then content else none) position).pack
  | .node okp left right =>
    let newOkp := okp.map fun kp => { kp with unmergedLeaves := kp.unmergedLeaves.filter pred }
    (LeftRightView.node newOkp (unAddP left pred) (unAddP right pred)).pack
termination_by l

/-- Port of `excluded_pre`. -/
public
def excludedPre (l: List Nat) (i: Nat): Bool :=
  !(l.contains i)

/-- Port of `un_add`. -/
public
def unAdd {l: Nat} (t: TreeKEM Bytes l) (excludedLeaves: List Nat): TreeKEM Bytes l :=
  unAddP t (excludedPre excludedLeaves)

/--
Port of `unmerged_leaves_resolution`.
MLS* requires each unmerged leaf to be a non-blank leaf of `t` (`unmerged_leaf_exists t`);
otherwise, the unmerged leaves that are not are skipped.
-/
public
def unmergedLeavesResolution {l: Nat} (t: TreeKEM Bytes l): List Nat → List Bytes
  | [] => []
  | hUl::tUl =>
    let rest := unmergedLeavesResolution t tUl
    if t.containsLeafIndex hUl then
      match leafAt t hUl with
      | some lp => lp.publicKey::rest
      | none => rest
    else
      rest

/--
Port of `tree_resolution`.
MLS* requires `treekem_invariant t`; otherwise, see `unmergedLeavesResolution`.
-/
public
def treeResolution {l: Nat} (t: TreeKEM Bytes l): List Bytes :=
  match t.intoLeftRightView with
  | .leaf none _ => []
  | .leaf (some mi) _ => [mi.publicKey]
  | .node (some kp) _ _ => kp.publicKey::(unmergedLeavesResolution t kp.unmergedLeaves)
  | .node none left right => treeResolution left ++ treeResolution right
termination_by l

/--
Port of `resolution_index`.
MLS* requires `Some? (leaf_at t li)`; otherwise, this function fails.
MLS* requires `treekem_invariant t`; otherwise, the result may be wrong (see `treeResolution`).
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def resolutionIndex {l: Nat} (t: TreeKEM Bytes l) (li: Nat): Result Nat :=
  match t.intoChildSiblingView li with
  | .leaf none _ => Result.internalFailure "resolution_index: leaf is blank"
  | .leaf (some _) _ => pure 0
  | .node (some kp) _ _ =>
    match kp.unmergedLeaves.idxOf? li with
    | none => pure 0
    | some res => pure (1+res)
  | .node none child sibling => do
    let childResolutionIndex ← resolutionIndex child li
    if child.position < sibling.position then
      pure childResolutionIndex
    else
      pure ((treeResolution sibling).length + childResolutionIndex)
termination_by l

/--
Port of `get_private_key`.
MLS* requires `treekem_priv_invariant t p_priv` (the leaf `li` is not blank);
otherwise, the private key of the leaf is returned.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def getPrivateKey {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (pPriv: TreeKEMPriv Bytes l): Result Bytes :=
  match t.intoChildSiblingView li, pPriv with
  | .leaf _ _, .leaf sk => pure sk
  | .node (some pn) _ _, .node optSk pNext =>
    if li < 2^32 && pn.unmergedLeaves.contains li then
      pure pNext.getPathLeaf
    else
      match optSk with
      | none => Result.error "get_private_key: private key not in private state"
      | some sk => pure sk
  | .node none child _, .node _ pNext =>
    getPrivateKey child li pNext
termination_by l

/--
Port of `check_update_path_ciphertexts_lengthes`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def checkUpdatePathCiphertextsLengthes {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathKEM Bytes l): Bool :=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf _ => true
  | .node _ child sibling, .node optUpn pNext =>
    let curOk :=
      match optUpn with
      | none => true
      | some upn => (treeResolution sibling).length == upn.encryptedPathSecret.val.length
    curOk && checkUpdatePathCiphertextsLengthes child li pNext
termination_by l

/--
Port of `get_path_secret`.
Obtain a path secret from a Commit.
MLS* requires `my_li <> li`; otherwise, this function fails.
MLS* requires `path_filtering_weak_ok t p_upd`; otherwise, this function may fail.
MLS* requires `check_update_path_ciphertexts_lengthes t p_upd`; otherwise, this function may fail.
MLS* requires `treekem_invariant t` and `treekem_priv_invariant t p_priv`; otherwise, see `resolutionIndex` and `getPrivateKey`.
MLS* requires `my_li: leaf_index l i` and `li: leaf_index l i`
(i.e. `t.containsLeafIndex myLi` and `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`, and branches when it leaves the subtree containing `myLi`.
-/
public
def getPathSecret {l: Nat} (t: TreeKEM Bytes l) (myLi li: Nat)
  (pPriv: TreeKEMPriv Bytes l) (pUpd: PathKEM Bytes l) (groupContext: GroupContext Bytes)
  : Result (Bytes × Nat)
:=
  match l, t.intoChildSiblingView li, pPriv, pUpd with
  | _, .leaf _ _, .leaf _, .leaf _ =>
    Result.internalFailure "get_path_secret: my_li and li are the same"
  | l+1, .node _ child sibling, .node _ pPrivNext, .node optUpn pUpdNext =>
    if child.containsLeafIndex myLi then
      -- The update path and the path to our leaf continue to the same node, recurse
      getPathSecret child myLi li pPrivNext pUpdNext groupContext
    else
      -- We are at a branching point
      match optUpn with
      | some upn => do
        -- Obtain the node secret by decryption
        let myIndex ← resolutionIndex sibling myLi
        let some myCiphertext := upn.encryptedPathSecret.val[myIndex]?
          | Result.internalFailure "get_path_secret: bad ciphertexts length"
        let myPrivateKey ← getPrivateKey sibling myLi pPrivNext
        let kemOutput ← mkHpkeKemOutput myCiphertext.kemOutput.val "get_path_secret" "kem_output"
        let pathSecret ← decryptWithLabel myPrivateKey "UpdatePathNode" (serializeNE GroupContext.mf groupContext) kemOutput myCiphertext.ciphertext.val
        pure (pathSecret, l+1)
      | none =>
        -- Impossible (MLS* proves it with `path_filtering_weak_ok`)
        Result.internalFailure "get_path_secret: no path node at the branching point"

/--
Port of `path_apply_path`.
This function can be used in two situations:
- when processing a Commit
- when processing a Welcome
When processing a Commit,
the tree `t` shoud already have the UpdatePath applied.
MLS* requires `0 < path_node_level <= l`; otherwise, this function fails.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def pathApplyPath {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (pPriv: TreeKEMPriv Bytes l)
  (pathSecret: Bytes) (pathNodeLevel: Nat)
  : Result (TreeKEMPriv Bytes l × Bytes)
:=
  match l, t.intoChildSiblingView li, pPriv with
  | _, .leaf _ _, .leaf _ =>
    Result.internalFailure "path_apply_path: path_node_level is not in the tree"
  | l+1, .node optPn child sibling, .node _ pPrivNext => do
    let (newPPrivNext, pathSecret) ←
      if pathNodeLevel = l+1 then
        pure (pPrivNext, pathSecret)
      else
        pathApplyPath child li pPrivNext pathSecret pathNodeLevel
    if !isTreeEmpty sibling then
      let (sk, pk) ← deriveKeypairFromPathSecret pathSecret
      let newPathSecret ← deriveNextPathSecret pathSecret
      if !(optPn.map (·.publicKey) == some pk) then
        Result.error "path_apply_path: wrong public key"
      else
        pure (.node (some sk) newPPrivNext, newPathSecret)
    else
      -- The node was filtered, transfer the path secret up in the tree
      pure (.node none newPPrivNext, pathSecret)
termination_by l

/--
Port of `generate_path_secrets`.
MLS*'s refinement on the result (`forget_path_secrets p == generate_forgotten_path_secrets t li`) is not ported.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def generatePathSecrets {l: Nat} (t: TreeKEM Bytes l) (leafSk: Bytes) (pathSecret0: Bytes) (li: Nat)
  : Result (PathSecrets Bytes l × Bytes)
:=
  match t.intoChildSiblingView li with
  | .leaf _ _ => pure (.leaf leafSk, pathSecret0)
  | .node _ child sibling => do
    let (pNext, myPathSecret) ← generatePathSecrets child leafSk pathSecret0 li
    if !isTreeEmpty sibling then
      let nextPathSecret ← deriveNextPathSecret myPathSecret
      pure (.node (some myPathSecret) pNext, nextPathSecret)
    else
      -- The node was filtered, transfer the path secret up in the tree
      pure (.node none pNext, myPathSecret)
termination_by l

/-- Port of `multi_encrypt_with_label_entropy_lengths`. -/
public
def multiEncryptWithLabelEntropyLengths: List Bytes → List Nat
  | [] => []
  | _::t => (CryptoBytes.hpkePrivateKeyLength Bytes)::(multiEncryptWithLabelEntropyLengths t)

/--
Port of `multi_encrypt_with_label`.
MLS* requires `rand: randomness bytes (multi_encrypt_with_label_entropy_lengths pks)`;
otherwise, this function fails when there is not enough randomness.
-/
public
def multiEncryptWithLabel: (publicKeys: List Bytes) → (label: String) → (context: Bytes) → (plaintext: Bytes) →
  Randomness Bytes → Result (List (HpkeCiphertext Bytes))
  | [], _, _, _, _ => pure []
  | pk::pks, label, context, plaintext, rand => do
    let (randCur, randNext) ← destRandomness rand
    let pk ← mkHpkePublicKey pk "multi_encrypt_with_label" "pk"
    let (kemOutput, ciphertext) ← encryptWithLabel pk label context plaintext randCur
    let kemOutput ← mkMlsBytes kemOutput "multi_encrypt_with_label" "kem_output"
    let ciphertext ← mkMlsBytes ciphertext "multi_encrypt_with_label" "ciphertext"
    let resTl ← multiEncryptWithLabel pks label context plaintext randNext
    pure ({ kemOutput, ciphertext }::resTl)

/--
Port of `encrypt_path_secrets_entropy_lengths`.
MLS* also takes `forget_path_secrets p` (the nodes having a path secret),
and only counts the randomness of these nodes.
This function counts the randomness of every node of the path:
nodes without a path secret are filtered, i.e. their sibling is empty, hence its resolution is empty
(this holds in `t` when it is obtained by un-adding leaves from the tree used to generate the path secrets, as in `finalizeCreateCommit`).
MLS* requires `treekem_invariant t`; otherwise, see `treeResolution`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def encryptPathSecretsEntropyLengths {l: Nat} (t: TreeKEM Bytes l) (li: Nat): List Nat :=
  match t.intoChildSiblingView li with
  | .leaf _ _ => []
  | .node _ child sibling =>
    let myRandomness := multiEncryptWithLabelEntropyLengths (treeResolution sibling)
    let nextRandomness := encryptPathSecretsEntropyLengths child li
    myRandomness ++ nextRandomness
termination_by l

/--
Port of `encrypt_path_secrets`.
MLS* requires `rand: randomness bytes (encrypt_path_secrets_entropy_lengths t (forget_path_secrets p))`
(i.e. `encryptPathSecretsEntropyLengths t li`);
otherwise, this function fails when there is not enough randomness.
MLS* requires `treekem_invariant t`; otherwise, see `treeResolution`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def encryptPathSecrets {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathSecrets Bytes l)
  (groupContext: GroupContext Bytes) (rand: Randomness Bytes)
  : Result (PathKEM Bytes l × TreeKEMPriv Bytes l)
:=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf leafIkm => do
    let (sk, pk) ← CryptoBytes.hpkeGenKeypair leafIkm
    pure (.leaf { publicKey := pk }, .leaf sk)
  | .node _ child _, .node none pNext => do
    let (resPNext, resPPrivNext) ← encryptPathSecrets child li pNext groupContext rand
    pure (.node none resPNext, .node none resPPrivNext)
  | .node _ child sibling, .node (some pathSecret) pNext => do
    let (randCur, randNext) ← splitRandomness (multiEncryptWithLabelEntropyLengths (treeResolution sibling)) rand
    let (resPNext, resPPrivNext) ← encryptPathSecrets child li pNext groupContext randNext
    let ciphertexts ← multiEncryptWithLabel (treeResolution sibling) "UpdatePathNode" (serializeNE GroupContext.mf groupContext) pathSecret randCur
    let ciphertexts ← mkMlsList ciphertexts "multi_encrypt_with_label" "ciphertexts"
    let (sk, pk) ← deriveKeypairFromPathSecret pathSecret
    let pk ← mkMlsBytes pk "encrypt_path_secrets" "pk"
    pure (.node (some { encryptionKey := pk, encryptedPathSecret := ciphertexts }) resPNext, .node (some sk) resPPrivNext)
termination_by l

/--
Port of `get_path_secret_of_added_leaf`.
Unlike MLS*, this function takes the tree `t` on which the path secrets were generated,
and follows the path with its child / sibling view.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def getPathSecretOfAddedLeaf {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathSecrets Bytes l) (leafLi: Nat): Result Bytes :=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf _ => Result.internalFailure "get_path_secret_of_added_leaf: leaf case"
  | .node _ child _, .node optPathSecret pNext =>
    if !t.containsLeafIndex leafLi then
      Result.internalFailure "get_path_secret_of_added_leaf: bad leaf index"
    else if child.containsLeafIndex leafLi then
      getPathSecretOfAddedLeaf child li pNext leafLi
    else
      match optPathSecret with
      | none => Result.internalFailure "get_path_secret_of_added_leaf: no path secret"
      | some pathSecret => pure pathSecret
termination_by l

/--
Port of `get_path_secret_of_added_leaves`.
Unlike MLS*, this function takes the tree `t` on which the path secrets were generated (see `getPathSecretOfAddedLeaf`).
-/
public
def getPathSecretOfAddedLeaves {l: Nat} (t: TreeKEM Bytes l) (li: Nat) (p: PathSecrets Bytes l) (leavesLi: List Nat): Result (List Bytes) :=
  leavesLi.mapM (getPathSecretOfAddedLeaf t li p)

/--
Port of `path_secrets_to_pre_pathkem`.
Unlike MLS*, this function also fails when a public key is too long to be an `HpkePublicKey Bytes`.
-/
public
def pathSecretsToPrePathkem: {l: Nat} → PathSecrets Bytes l → Result (PrePathKEM Bytes l)
  | _, .leaf leafSk => do
    let (_, pk) ← CryptoBytes.hpkeGenKeypair leafSk
    pure (.leaf { publicKey := pk })
  | _, .node none pNext => do
    let resPNext ← pathSecretsToPrePathkem pNext
    pure (.node none resPNext)
  | _, .node (some pathSecret) pNext => do
    let resPNext ← pathSecretsToPrePathkem pNext
    let (_, pk) ← deriveKeypairFromPathSecret pathSecret
    let pk ← mkMlsBytes pk "path_secrets_to_pre_pathkem" "pk"
    pure (.node (some pk) resPNext)

/-- Port of `create_empty_priv`. -/
public
def createEmptyPriv: {l: Nat} → (leafPrivateKey: Bytes) → TreeKEMPriv Bytes l
  | 0, leafPrivateKey => .leaf leafPrivateKey
  | _+1, leafPrivateKey => .node none (createEmptyPriv leafPrivateKey)

end CryptoBytes

/--
Port of `compute_least_common_ancestor_level`.
Unlike MLS*, this function takes the tree `t` of the path, and follows the path with its child / sibling view.
MLS* requires `leaf_ind <> li`; otherwise, this function returns `0`.
MLS* requires `leaf_ind: leaf_index l i` (i.e. `t.containsLeafIndex leafInd`); otherwise, this function returns `l`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
public
def computeLeastCommonAncestorLevel {TreeLeaf TreeNode Leaf Node: Type} {l: Nat}
  (t: Tree TreeLeaf TreeNode l) (li: Nat) (p: Path Leaf Node l) (leafInd: Nat): Nat
:=
  match l, t.intoChildSiblingView li, p with
  | _, .leaf _ _, .leaf _ => 0
  | l+1, .node _ child _, .node _ pNext =>
    if child.containsLeafIndex leafInd then
      computeLeastCommonAncestorLevel child li pNext leafInd
    else
      l+1

end MLS.TreeKEM
