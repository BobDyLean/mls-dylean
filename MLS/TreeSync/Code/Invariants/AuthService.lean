module

public import MLS.Common.Code.TreeCommon
public import MLS.TreeSync.Code.Types

/-!
Port of `MLS.TreeSync.Invariants.AuthService`.

Abstraction for the Authentication Service (AS).
The goal for the AS is to verify that a signature public key belong to some credential.
To make no assumption on how it is implemented, we abstract it away:
- when a signature public key and a credential is validated by the AS, it gives a token of type `TokenT`,
- we also obtain some relationship between the signature public key, credential and the token (`credentialOk`).
We store tokens for every leaf with the `ASTokens` type,
and have the invariant that every leaf identity has been validated by the AS, using the tokens.
At the end, there are several instantiations for `ASParameters`:
- in the DY* proofs,
- in the executable, concrete MLS API.

Port-specific differences:
- `as_tokens bytes token_t` does not take `Bytes` as a parameter (MLS* does not use it).
- `ASParameters Bytes TokenT` takes the type of tokens as a parameter (a field `token_t` in MLS*).
- The tree positions of a TreeSync tree and its tokens are not bound by the types
  (MLS*'s `treesync bytes tkt l i` and `as_tokens bytes token_t l i` share `i`):
  lemmas take a hypothesis `ts.position = ast.position`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `as_input`. -/
public
abbrev ASInput (Bytes: Type) [BytesLike Bytes] :=
  SignaturePublicKey Bytes × Credential Bytes

/-- Port of `leaf_node_to_as_input`. -/
@[expose]
public
def leafNodeToAsInput (ln: LeafNode Bytes tkt): ASInput Bytes :=
  (ln.data.signatureKey, ln.data.credential)

/--
Port of `as_parameters`.
Unlike MLS*, the type of tokens `TokenT` is a parameter (MLS*'s field `token_t`),
so that parameters with the same tokens can be compared without casts (see `asParametersWeaker`).
-/
public
structure ASParameters (Bytes: Type) [BytesLike Bytes] (TokenT: Type) where
  credentialOk: ASInput Bytes → TokenT → Prop
  validSuccessor: ASInput Bytes → ASInput Bytes → Prop

/--
Port of `as_tokens`.
An array of tokens for every leaf of a tree.
Internally it's defined as a tree with no internal node content,
because it's easier to manipulate with TreeSync like that in the proofs
-/
public
abbrev ASTokens (TokenT: Type) :=
  Tree (Option TokenT) Unit

variable {TokenT: Type}

/--
Port of `as_add_update`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def asAddUpdate {l: Nat} (t: ASTokens TokenT l) (li: Nat) (token: TokenT): ASTokens TokenT l :=
  treeChangePath t li (some token) ()

/--
Port of `as_remove`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def asRemove {l: Nat} (t: ASTokens TokenT l) (li: Nat): ASTokens TokenT l :=
  treeChangePath t li none ()

/-- Port of `as_truncate`. -/
@[expose]
public
def asTruncate {l: Nat} (t: ASTokens TokenT (l+1)): ASTokens TokenT l :=
  t.left

/-- Port of `as_extend`. -/
@[expose]
public
def asExtend {l: Nat} (t: ASTokens TokenT l): ASTokens TokenT (l+1) :=
  (LeftRightView.node () t (mkBlankTreeGeneral l (t.position + 2^l) none ())).pack

/--
Port of `one_credential_ok`.
MLS* requires `li: leaf_index l i` (i.e. `ts.containsLeafIndex li`);
otherwise, it is about the leaves closest to `li`.
-/
@[expose]
public
def oneCredentialOk (asp: ASParameters Bytes TokenT) {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l) (li: Nat): Prop :=
  match leafAt ts li, leafAt ast li with
  | some ln, some asToken => asp.credentialOk (leafNodeToAsInput ln) asToken
  | none, none => True
  | _, _ => False

/--
Port of `all_credentials_ok`.
The authentication service invariant:
Every non-blank leaf is associated with a token that attests its identity was validated by the AS.
-/
@[expose]
public
def allCredentialsOk (asp: ASParameters Bytes TokenT) {l: Nat} (ts: TreeSync Bytes tkt l) (ast: ASTokens TokenT l): Prop :=
  match ts.intoLeftRightView, ast.intoLeftRightView with
  | .leaf none _, .leaf none _ => True
  | .leaf (some ln) _, .leaf (some asToken) _ => asp.credentialOk (leafNodeToAsInput ln) asToken
  | .leaf _ _, .leaf _ _ => False
  | .node _ sleft sright, .node _ astleft astright =>
    allCredentialsOk asp sleft astleft ∧ allCredentialsOk asp sright astright
termination_by l

end MLS.TreeSync
