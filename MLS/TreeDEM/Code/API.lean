module

public import MLS.TreeDEM.Code.Message.Framing
public import MLS.TreeDEM.Code.API.Types

/-!
Port of `MLS.TreeDEM.API`.

Port-specific differences:
- The namespace is `MLS.TreeDEM.API` (MLS* refers to these functions as `MLS.TreeDEM.API.init`, …).
- The refinements on the results (e.g. `res.wire_format == wf /\ res.content == msg`) are not ported.
- Signature nonces and reuse guards are `Bytes` (see `MLS.Crypto.Builtins`).
-/

namespace MLS.TreeDEM.API

open Comparse
open MLS MLS.TreeSync

/--
Port of `treedem_init_arguments`.
`my_leaf_index` is a `Nat` (MLS*'s `leaf_index tree_height 0`).
-/
public
structure TreeDEMInitArguments (Bytes: Type) [BytesLike Bytes] where
  treeHeight: Nat
  myLeafIndex: Nat
  groupContext: GroupContext Bytes
  encryptionSecret: Bytes
  senderDataSecret: Bytes
  membershipKey: Bytes
  mySignatureKey: Bytes
  verificationKeys: Tree (Option (SignaturePublicKey Bytes)) Unit treeHeight

variable {Bytes: Type} [CryptoBytes Bytes]

/--
Port of `init`.
MLS* requires `my_leaf_index: leaf_index tree_height 0` (i.e. `myLeafIndex < 2^treeHeight`); otherwise, see `leafKdf`.
-/
public
def init (args: TreeDEMInitArguments Bytes): Result (TreeDEMState Bytes) := do
  let { treeHeight, myLeafIndex, groupContext, encryptionSecret, senderDataSecret, membershipKey, mySignatureKey, verificationKeys } := args
  let leafTreeSecret ← leafKdf encryptionSecret treeHeight 0 myLeafIndex
  let myApplicationRatchet ← initApplicationRatchet leafTreeSecret
  let myHandshakeRatchet ← initHandshakeRatchet leafTreeSecret
  pure {
    treeHeight
    myLeafIndex
    groupContext
    encryptionSecret
    senderDataSecret
    membershipKey
    mySignatureKey
    myHandshakeRatchet
    myApplicationRatchet
    verificationKeys
  }

/-! ## Authentication -/

/-!
Proposals and application messages are authenticated using a single signature.
This function will compute it.
-/

/--
Port of `authenticate_non_commit`.
MLS* requires `msg.content.content_type =!= CT_commit`; otherwise, this function fails.
-/
public
def authenticateNonCommit (st: TreeDEMState Bytes) (wf: WireFormat) (msg: FramedContent Bytes) (nonce: Bytes):
  Result (AuthenticatedContent Bytes)
:= do
  let signature ← computeMessageSignature st.mySignatureKey nonce wf msg (StaticOption.mk st.groupContext)
  let confirmationTag ← StaticOption.mkM (msg.content.contentType == .commit) fun _ =>
    Result.internalFailure "authenticate_non_commit: the message is a commit"
  pure {
    wireFormat := wf
    content := msg
    auth := {
      signature
      confirmationTag
    }
  }

/-!
Commits are authenticated using both a signature and a confirmation tag.
Because the confirmation tag is computed using the next epoch's confirmation key,
which itself depend on the confirmed transcript hash,
which itself depend on the commit's signature,
commits are authenticated in two steps:
first the signature,
then the confirmation tag.
-/

/--
Port of `start_authenticate_commit`.
MLS* requires `msg.content.content_type == CT_commit`; this function does not need it.
-/
public
def startAuthenticateCommit (st: TreeDEMState Bytes) (wf: WireFormat) (msg: FramedContent Bytes) (nonce: Bytes):
  Result (ConfirmedTranscriptHashInput Bytes)
:= do
  let signature ← computeMessageSignature st.mySignatureKey nonce wf msg (StaticOption.mk st.groupContext)
  pure {
    wireFormat := wf
    content := msg
    signature
  }

/--
Port of `finish_authenticate_commit`.
MLS* requires `msg.content.content.content_type == CT_commit`; otherwise, this function fails.
-/
public
def finishAuthenticateCommit (msg: ConfirmedTranscriptHashInput Bytes) (confirmationTag: Bytes): Result (AuthenticatedContent Bytes) :=
  if !(msg.content.content.contentType == .commit) then
    Result.internalFailure "finish_authenticate_commit: not a commit"
  else if h: mlsNatPred (BytesLike.length confirmationTag) then do
    let confirmationTag ← StaticOption.mkM (msg.content.content.contentType == .commit) fun _ =>
      pure ⟨confirmationTag, h⟩
    pure {
      wireFormat := msg.wireFormat
      content := msg.content
      auth := {
        signature := msg.signature
        confirmationTag
      }
    }
  else
    Result.error "finish_authenticate_commit: confirmation_tag too long"

/-! Functions to verify the authentication. -/

/-- Port of `verify_signature`. -/
public
def verifySignature (st: TreeDEMState Bytes) (msg: AuthenticatedContent Bytes): Bool :=
  let optVerifKey :=
    match msg.content.sender with
    | .member leafIndex =>
      if !(leafIndex.toNat < 2^st.treeHeight) then none
      else leafAt st.verificationKeys leafIndex.toNat
    | _ => none -- TODO (as in MLS*)
  match optVerifKey with
  | none => false
  | some verifKey =>
    checkMessageSignature verifKey.val msg.auth.signature.val msg.wireFormat msg.content (StaticOption.mk st.groupContext)

/-- Port of `verify_confirmation_tag`. -/
public
def verifyConfirmationTag (_st: TreeDEMState Bytes) (msg: AuthenticatedContent Bytes) (confirmationTag: Bytes): Result Bool :=
  if h: msg.content.content.contentType == .commit then
    pure ((msg.auth.confirmationTag.get h).val == confirmationTag)
  else
    Result.internalFailure "verify_confirmation_tag: not a commit"

/-! ## Protection -/

/-! Protect public messages, by computing or checking the membership tag -/

/--
Port of `protect_public`.
MLS* requires `msg.wire_format == WF_mls_public_message`; this function does not need it.
-/
public
def protectPublic (st: TreeDEMState Bytes) (msg: AuthenticatedContent Bytes): Result (PublicMessage Bytes) :=
  authenticatedContentToPublicMessage msg (StaticOption.mk st.groupContext) (StaticOption.mk st.membershipKey)

/-- Port of `unprotect_public`. -/
public
def unprotectPublic (st: TreeDEMState Bytes) (msg: PublicMessage Bytes): Result (AuthenticatedContent Bytes) :=
  publicMessageToAuthenticatedContent msg (StaticOption.mk st.groupContext) (StaticOption.mk st.membershipKey)

/-!
Protect private messages, by encrypting using the secret tree.
These functions are stateful, for forward secrecy.
-/

/--
Port of `protect_private`.
MLS* requires `msg.wire_format == WF_mls_private_message`; this function does not need it.
MLS* requires `reuse_guard` to have length `4`; otherwise, this function fails.
-/
public
def protectPrivate (st: TreeDEMState Bytes) (msg: AuthenticatedContent Bytes) (reuseGuard: Bytes):
  Result (PrivateMessage Bytes × TreeDEMState Bytes)
:= do
  let ratchet :=
    match msg.content.content.contentType with
    | .application => st.myApplicationRatchet
    | _ => st.myHandshakeRatchet
  let (res, newRatchet) ← authenticatedContentToPrivateMessage msg ratchet reuseGuard st.senderDataSecret
  let newSt :=
    match msg.content.content.contentType with
    | .application => { st with myApplicationRatchet := newRatchet }
    | _ => { st with myHandshakeRatchet := newRatchet }
  pure (res, newSt)

/-- Port of `unprotect_private`. -/
public
def unprotectPrivate (st: TreeDEMState Bytes) (msg: PrivateMessage Bytes): Result (AuthenticatedContent Bytes × TreeDEMState Bytes) := do
  let res ← privateMessageToAuthenticatedContent msg st.treeHeight st.encryptionSecret st.senderDataSecret
  pure (res, st)

end MLS.TreeDEM.API
