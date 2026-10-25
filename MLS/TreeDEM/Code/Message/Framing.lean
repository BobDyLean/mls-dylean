import MLS.TreeDEM.Code.NetworkTypes
import MLS.TreeDEM.Code.Keys

/-!
Port of `MLS.TreeDEM.Message.Framing`.

Port-specific differences:
- `knows_group_context` is `Sender.hasGroupContext`, and `S_member?` is `Sender.isMember`
  (both in `MLS.TreeDEM.NetworkTypes`).
- Functions taking a group context as `static_option (S_member? sender) _` get it with `StaticOption.get`,
  and pass it to `computeTbs` with `StaticOption.mk` (MLS* uses the subtyping `S_member? ⟹ knows_group_context`).
- AEAD keys and nonces, and reuse guards are `Bytes` (see `MLS.Crypto.Builtins`).
- `apply_reuse_guard` is the field `CryptoBytes.applyReuseGuard` (replacing MLS*'s `xor`).
-/

namespace MLS.TreeDEM

open Comparse
open MLS

/-! ## Authentication -/

section BytesLike

variable {Bytes: Type} [BytesLike Bytes]

/-- Port of `compute_tbs`. -/
def computeTbs (wireFormat: WireFormat) (content: FramedContent Bytes)
  (groupContext: StaticOption content.sender.hasGroupContext (GroupContext Bytes)): FramedContentTBS Bytes
:=
  {
    version := .mls10
    wireFormat
    content
    groupContext
  }

/--
Port of `compute_tbm`.
MLS* requires `S_member? content.sender`; this function does not need it.
-/
def computeTbm (content: FramedContent Bytes) (auth: FramedContentAuthData Bytes content.content.contentType)
  (groupContext: GroupContext Bytes): AuthenticatedContentTBM Bytes
:=
  let contentTbs := computeTbs .mlsPublicMessage content (StaticOption.mk groupContext)
  {
    contentTbs
    auth
  }

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `compute_message_signature`. -/
def computeMessageSignature (sk: Bytes) (rand: Bytes) (wireFormat: WireFormat) (msg: FramedContent Bytes)
  (groupContext: StaticOption msg.sender.hasGroupContext (GroupContext Bytes)): Result (MlsBytes Bytes)
:= do
  let tbs := computeTbs wireFormat msg groupContext
  let serializedTbs := serializeNE FramedContentTBS.mf tbs
  let signature ← signWithLabel sk "FramedContentTBS" serializedTbs rand
  mkMlsBytes signature "compute_message_signature" "signature"

/-- Port of `check_message_signature`. -/
def checkMessageSignature (pk: Bytes) (signature: Bytes) (wireFormat: WireFormat) (msg: FramedContent Bytes)
  (groupContext: StaticOption msg.sender.hasGroupContext (GroupContext Bytes)): Bool
:=
  let tbs := computeTbs wireFormat msg groupContext
  let serializedTbs := serializeNE FramedContentTBS.mf tbs
  verifyWithLabel pk "FramedContentTBS" serializedTbs signature

/--
Port of `compute_message_membership_tag`.
MLS* requires `S_member? msg.sender`; this function does not need it.
-/
def computeMessageMembershipTag (membershipKey: Bytes) (msg: FramedContent Bytes)
  (auth: FramedContentAuthData Bytes msg.content.contentType) (groupContext: GroupContext Bytes): Result Bytes
:=
  let tbm := computeTbm msg auth groupContext
  let serializedTbm := serializeNE AuthenticatedContentTBM.mf tbm
  CryptoBytes.hmacHmac membershipKey serializedTbm

/-- Port of `check_authenticated_content_signature`. -/
def checkAuthenticatedContentSignature (msg: AuthenticatedContent Bytes) (vk: Bytes)
  (groupContext: StaticOption msg.content.sender.hasGroupContext (GroupContext Bytes)): Bool
:=
  checkMessageSignature vk msg.auth.signature.val msg.wireFormat msg.content groupContext

/-! ## From/to public message -/

/-- Port of `public_message_to_authenticated_content`. -/
def publicMessageToAuthenticatedContent (pt: PublicMessage Bytes)
  (groupContext: StaticOption pt.content.sender.isMember (GroupContext Bytes))
  (membershipKey: StaticOption pt.content.sender.isMember Bytes)
  : Result (AuthenticatedContent Bytes)
:= do
  let membershipTagOk ←
    if h: pt.content.sender.isMember then do
      let expectedMembershipTag ← computeMessageMembershipTag (membershipKey.get h) pt.content pt.auth (groupContext.get h)
      pure ((pt.membershipTag.get h).val == expectedMembershipTag)
    else
      pure true
  if !membershipTagOk then
    Result.error "public_message_to_authenticated_content: bad membership tag"
  else
    pure {
      wireFormat := .mlsPublicMessage
      content := pt.content
      auth := pt.auth
    }

/--
Port of `authenticated_content_to_public_message`.
MLS* requires `auth_msg.wire_format == WF_mls_public_message`; this function does not need it.
Unlike MLS*, this function fails when the membership tag is too long to be a `Mac Bytes`.
-/
def authenticatedContentToPublicMessage (authMsg: AuthenticatedContent Bytes)
  (groupContext: StaticOption authMsg.content.sender.isMember (GroupContext Bytes))
  (membershipKey: StaticOption authMsg.content.sender.isMember Bytes)
  : Result (PublicMessage Bytes)
:= do
  let membershipTag ← StaticOption.mkM authMsg.content.sender.isMember fun h => do
    let res ← computeMessageMembershipTag (membershipKey.get h) authMsg.content authMsg.auth (groupContext.get h)
    mkMlsBytes res "authenticated_content_to_public_message" "membership_tag"
  pure {
    content := authMsg.content
    auth := authMsg.auth
    membershipTag
  }

/-! ## From/to private message -/

/-- Port of `get_ciphertext_sample`. -/
def getCiphertextSample (ct: Bytes): Bytes :=
  let len := CryptoBytes.kdfLength Bytes
  if BytesLike.length ct ≤ len then
    ct
  else
    match BytesLike.split ct len with
    | some (sample, _) => sample
    | none => ct

end CryptoBytes

section BytesLike

variable {Bytes: Type} [BytesLike Bytes]

/--
Port of `private_framed_content_to_sender_data_aad`.
Used in decryption
-/
def privateFramedContentToSenderDataAad (ct: PrivateMessage Bytes): SenderDataAAD Bytes :=
  {
    groupId := ct.groupId
    epoch := ct.epoch
    contentType := ct.contentType
  }

/--
Port of `framed_content_to_sender_data_aad`.
Used in encryption
-/
def framedContentToSenderDataAad (content: FramedContent Bytes): SenderDataAAD Bytes :=
  {
    groupId := content.groupId
    epoch := content.epoch
    contentType := content.content.contentType
  }

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `sender_data_key_nonce`. -/
def senderDataKeyNonce (ciphertextSample: Bytes) (senderDataSecret: Bytes): Result (Bytes × Bytes) := do
  let senderDataKey ← expandWithLabel senderDataSecret "key" ciphertextSample (CryptoBytes.aeadKeyLength Bytes)
  let senderDataNonce ← expandWithLabel senderDataSecret "nonce" ciphertextSample (CryptoBytes.aeadNonceLength Bytes)
  pure (senderDataKey, senderDataNonce)

/-- Port of `decrypt_sender_data`. -/
def decryptSenderData (ad: SenderDataAAD Bytes) (ciphertextSample: Bytes) (senderDataSecret: Bytes) (encryptedSenderData: Bytes):
  Result (SenderData Bytes)
:= do
  let (senderDataKey, senderDataNonce) ← senderDataKeyNonce ciphertextSample senderDataSecret
  let senderData ← CryptoBytes.aeadDecrypt senderDataKey senderDataNonce (serializeNE SenderDataAAD.mf ad) encryptedSenderData
  Result.fromOption "decrypt_sender_data: malformed sender data" (SenderData.mf.toExtensible.parse senderData)

/-- Port of `encrypt_sender_data`. -/
def encryptSenderData (ad: SenderDataAAD Bytes) (ciphertextSample: Bytes) (senderDataSecret: Bytes) (senderData: SenderData Bytes):
  Result Bytes
:= do
  let (senderDataKey, senderDataNonce) ← senderDataKeyNonce ciphertextSample senderDataSecret
  CryptoBytes.aeadEncrypt senderDataKey senderDataNonce (serializeNE SenderDataAAD.mf ad) (serializeNE SenderData.mf senderData)

end CryptoBytes

/--
Port of `private_message_to_private_content_aad`.
Used in decryption
-/
def privateMessageToPrivateContentAad {Bytes: Type} [BytesLike Bytes] (ct: PrivateMessage Bytes): PrivateContentAAD Bytes :=
  {
    groupId := ct.groupId
    epoch := ct.epoch
    contentType := ct.contentType
    authenticatedData := ct.authenticatedData
  }

/--
Port of `framed_content_to_private_content_aad`.
Used in encryption
-/
def framedContentToPrivateContentAad {Bytes: Type} [BytesLike Bytes] (content: FramedContent Bytes): PrivateContentAAD Bytes :=
  {
    groupId := content.groupId
    epoch := content.epoch
    contentType := content.content.contentType
    authenticatedData := content.authenticatedData
  }

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `decrypt_private_message_content`. -/
def decryptPrivateMessageContent (ad: PrivateContentAAD Bytes) (key: Bytes) (nonce: Bytes) (ct: Bytes):
  Result (PrivateMessageContent Bytes ad.contentType)
:= do
  let ciphertextContent ← CryptoBytes.aeadDecrypt key nonce (serializeNE PrivateContentAAD.mf ad) ct
  Result.fromOption "decrypt_private_message_content: malformed ciphertext content"
    ((PrivateMessageContent.mf ad.contentType).parse ciphertextContent)

/-- Port of `encrypt_private_message_content`. -/
def encryptPrivateMessageContent (ad: PrivateContentAAD Bytes) (key: Bytes) (nonce: Bytes)
  (pt: PrivateMessageContent Bytes ad.contentType): Result Bytes
:=
  CryptoBytes.aeadEncrypt key nonce (serializeNE PrivateContentAAD.mf ad) ((PrivateMessageContent.mf ad.contentType).serialize pt)

/-- Port of `private_message_to_authenticated_content`. -/
def privateMessageToAuthenticatedContent (ct: PrivateMessage Bytes) (l: Nat) (encryptionSecret: Bytes) (senderDataSecret: Bytes):
  Result (AuthenticatedContent Bytes)
:= do
  let senderData ← do
    let senderDataAd := privateFramedContentToSenderDataAad ct
    decryptSenderData senderDataAd (getCiphertextSample ct.ciphertext.val) senderDataSecret ct.encryptedSenderData.val
  let rsOutput ← do
    let senderIndex ←
      if !(senderData.leafIndex.toNat < 2^l) then
        Result.error "private_message_to_authenticated_content: leaf_index too big"
      else
        pure senderData.leafIndex.toNat
    let leafTreeSecret ← leafKdf encryptionSecret l 0 senderIndex
    let initRatchet ←
      match ct.contentType with
      | .application => initApplicationRatchet leafTreeSecret
      | _ => initHandshakeRatchet leafTreeSecret
    ratchetGetGenerationKey initRatchet senderData.generation.toNat
  let ciphertextContent ← do
    let nonce := rsOutput.nonce
    let key := rsOutput.key
    let patchedNonce ← CryptoBytes.applyReuseGuard senderData.reuseGuard.val nonce
    let ciphertextContentAd := privateMessageToPrivateContentAad ct
    decryptPrivateMessageContent ciphertextContentAd key patchedNonce ct.ciphertext.val
  pure {
    wireFormat := .mlsPrivateMessage
    content := {
      groupId := ct.groupId
      epoch := ct.epoch
      sender := .member senderData.leafIndex
      authenticatedData := ct.authenticatedData
      content := {
        contentType := ct.contentType
        content := ciphertextContent.data.content
      }
    }
    auth := {
      signature := ciphertextContent.data.auth.signature
      confirmationTag := ciphertextContent.data.auth.confirmationTag
    }
  }

/--
Port of `authenticated_content_to_private_message`.
MLS* requires `msg.wire_format == WF_mls_private_message`; this function does not need it.
MLS* requires `reuse_guard` to have length `4`; otherwise, this function fails.
-/
def authenticatedContentToPrivateMessage (authMsg: AuthenticatedContent Bytes) (ratchet: RatchetState Bytes)
  (reuseGuard: Bytes) (senderDataSecret: Bytes)
  : Result (PrivateMessage Bytes × RatchetState Bytes)
:= do
  let ciphertext ← do
    let keyNonce ← ratchetGetKey ratchet
    let key := keyNonce.key
    let patchedNonce ← CryptoBytes.applyReuseGuard reuseGuard keyNonce.nonce
    let ciphertextContent: PrivateMessageContent Bytes authMsg.content.content.contentType := {
      data := {
        content := authMsg.content.content.content
        auth := authMsg.auth
      }
      padding := [] -- TODO (as in MLS*)
    }
    let ciphertextContentAd := framedContentToPrivateContentAad authMsg.content
    let ciphertext ← encryptPrivateMessageContent ciphertextContentAd key patchedNonce ciphertextContent
    mkMlsBytes ciphertext "authenticated_content_to_private_message" "encrypted_sender_data"
  let encryptedSenderData ←
    match authMsg.content.sender with
    | .member leafIndex => do
      let generation ← mkUInt32 ratchet.generation "authenticated_content_to_private_message" "generation"
      let reuseGuard ←
        if h: BytesLike.length reuseGuard = 4 then pure ⟨reuseGuard, h⟩
        else Result.internalFailure "authenticated_content_to_private_message: reuse_guard must have length 4"
      let senderDataAd := framedContentToSenderDataAad authMsg.content
      let senderData := {
        leafIndex
        generation
        reuseGuard
      }
      let encryptedSenderData ← encryptSenderData senderDataAd (getCiphertextSample ciphertext.val) senderDataSecret senderData
      mkMlsBytes encryptedSenderData "authenticated_content_to_private_message" "encrypted_sender_data"
    | _ => Result.error "authenticated_content_to_private_message: sender is not a member"
  let newRatchet ← ratchetNextState ratchet
  pure ({
    groupId := authMsg.content.groupId
    epoch := authMsg.content.epoch
    contentType := authMsg.content.content.contentType
    authenticatedData := authMsg.content.authenticatedData
    encryptedSenderData
    ciphertext
  }, newRatchet)

end CryptoBytes

end MLS.TreeDEM
