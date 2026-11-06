module

public import MLS.Common.Code.Tree
public import MLS.TreeSync.Code.Types
public import MLS.TreeKEM.Code.KeySchedule
public import MLS.Bootstrap.Code.KeyPackageRef

/-!
Port of `MLS.Bootstrap.Welcome`.

Port-specific differences:
- AEAD keys and nonces, HPKE keys and signature nonces are `Bytes` (see `MLS.Crypto.Builtins`).
-/

namespace MLS.Bootstrap

open Comparse
open MLS
open MLS.TreeSync MLS.TreeKEM

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-! ## Utility functions -/

/-- Port of `welcome_secret_to_key`. -/
public
def welcomeSecretToKey (welcomeSecret: Bytes): Result Bytes :=
  expandWithLabel welcomeSecret "key" BytesLike.empty (CryptoBytes.aeadKeyLength Bytes)

/-- Port of `welcome_secret_to_nonce`. -/
public
def welcomeSecretToNonce (welcomeSecret: Bytes): Result Bytes :=
  expandWithLabel welcomeSecret "nonce" BytesLike.empty (CryptoBytes.aeadNonceLength Bytes)

/-! ## Decrypting a welcome -/

/-- Port of `find_my_encrypted_group_secret`. -/
public
def findMyEncryptedGroupSecret {a: Type} (kpRefToKpSecrets: Bytes → Option a):
  List (EncryptedGroupSecrets Bytes) → Option (KeyPackageRef Bytes × a × HpkeCiphertext Bytes)
  | [] => none
  | h::t =>
    match kpRefToKpSecrets h.newMember.val with
    | some kpSecrets => some (h.newMember, kpSecrets, h.encryptedGroupSecrets)
    | none => findMyEncryptedGroupSecret kpRefToKpSecrets t

/-- Port of `_decrypt_group_secrets` (Lean identifiers cannot start with `_`). -/
public
def decryptGroupSecrets' (myHpkeSk: Bytes) (myHpkeCiphertext: HpkeCiphertext Bytes) (ad: Bytes): Result (GroupSecrets Bytes) := do
  let kemOutput ← mkHpkeKemOutput myHpkeCiphertext.kemOutput.val "decrypt_welcome" "kem_output"
  let groupSecretsBytes ← decryptWithLabel myHpkeSk "Welcome" ad kemOutput myHpkeCiphertext.ciphertext.val
  Result.fromOption "decrypt_group_secrets: malformed group secrets" (GroupSecrets.mf.toExtensible.parse groupSecretsBytes)

/-- Port of `decrypt_group_secrets`. -/
public
def decryptGroupSecrets {a: Type} (w: Welcome Bytes) (kpRefToKpSecrets: Bytes → Option a) (kpSecretsToHpkeSk: a → Result Bytes):
  Result (GroupSecrets Bytes × (KeyPackageRef Bytes × a))
:= do
  let (myKpRef, myKpSecrets, myHpkeCiphertext) ←
    Result.fromOption "decrypt_welcome: can't find my encrypted secret" (findMyEncryptedGroupSecret kpRefToKpSecrets w.secrets.val)
  let myHpkeSk ← kpSecretsToHpkeSk myKpSecrets
  let groupSecrets ← decryptGroupSecrets' myHpkeSk myHpkeCiphertext w.encryptedGroupInfo.val
  pure (groupSecrets, (myKpRef, myKpSecrets))

/-- Port of `decrypt_group_info`. -/
public
def decryptGroupInfo (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (encryptedGroupInfo: Bytes):
  Result (GroupInfo Bytes)
:= do
  let welcomeSecret ← secretJoinerToWelcome joinerSecret psks
  let welcomeKey ← welcomeSecretToKey welcomeSecret
  let welcomeNonce ← welcomeSecretToNonce welcomeSecret
  let groupInfoBytes ← CryptoBytes.aeadDecrypt welcomeKey welcomeNonce BytesLike.empty encryptedGroupInfo
  Result.fromOption "decrypt_group_info: malformed group info" (GroupInfo.mf.toExtensible.parse groupInfoBytes)

/-! ## Encrypting a welcome -/

/-- Port of `encrypt_one_group_secrets`. -/
public
def encryptOneGroupSecrets (kp: KeyPackage Bytes TreeKEM.tkt) (encryptedGroupInfo: Bytes) (gs: GroupSecrets Bytes) (rand: Bytes):
  Result (EncryptedGroupSecrets Bytes)
:= do
  let kpRef ← computeKeyPackageRef kp
  let gsBytes := serializeNE GroupSecrets.mf gs
  let leafHpkePk ← mkHpkePublicKey kp.tbs.initKey.val "encrypt_one_group_secrets" "leaf_hpke_pk"
  let (kemOutput, ciphertext) ← encryptWithLabel leafHpkePk "Welcome" encryptedGroupInfo gsBytes rand
  let kemOutput ← mkMlsBytes kemOutput "encrypt_one_group_secrets" "kem_output"
  let ciphertext ← mkMlsBytes ciphertext "encrypt_one_group_secrets" "ciphertext"
  pure {
    newMember := kpRef
    encryptedGroupSecrets := {
      kemOutput
      ciphertext
    }
  }

/-- Port of `encrypt_welcome_entropy_length`. -/
@[expose]
public
def encryptWelcomeEntropyLength: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes) → List Nat
  | [] => []
  | _::t => (CryptoBytes.hpkePrivateKeyLength Bytes)::encryptWelcomeEntropyLength t

end CryptoBytes

/-- Port of `mk_group_secrets`. -/
public
def mkGroupSecrets {Bytes: Type} [BytesLike Bytes]
  (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes)) (pathSecret: Option Bytes): Result (GroupSecrets Bytes)
:= do
  let joinerSecret ← mkMlsBytes joinerSecret "mk_group_secrets" "joiner_secret"
  let pathSecret ←
    match pathSecret with
    | none => pure none
    | some pathSecret => do
      let pathSecret ← mkMlsBytes pathSecret "mk_group_secrets" "path_secret"
      pure (some { pathSecret })
  let psks ← mkMlsList psks "mk_group_secrets" "psks"
  pure {
    joinerSecret
    pathSecret
    psks
  }

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/--
Port of `encrypt_group_secrets`.
MLS* requires `rand: randomness bytes (encrypt_welcome_entropy_length key_packages)`;
otherwise, this function fails when there is not enough randomness.
-/
public
def encryptGroupSecrets (encryptedGroupInfo: Bytes) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes)):
  (keyPackages: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes)) → Randomness Bytes → Result (List (EncryptedGroupSecrets Bytes))
  | [], _ => pure []
  | (kp, pathSecret)::tail, rand => do
    let (curRand, randNext) ← destRandomness rand
    let groupSecrets ← mkGroupSecrets joinerSecret psks pathSecret
    let resHead ← encryptOneGroupSecrets kp encryptedGroupInfo groupSecrets curRand
    let resTail ← encryptGroupSecrets encryptedGroupInfo joinerSecret psks tail randNext
    pure (resHead::resTail)

/-- Port of `encrypt_group_info`. -/
public
def encryptGroupInfo (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (groupInfo: GroupInfo Bytes):
  Result (MlsBytes Bytes)
:= do
  let welcomeSecret ← secretJoinerToWelcome joinerSecret psks
  let welcomeKey ← welcomeSecretToKey welcomeSecret
  let welcomeNonce ← welcomeSecretToNonce welcomeSecret
  let groupInfoBytes := serializeNE GroupInfo.mf groupInfo
  let encryptedWelcomeGroupInfo ← CryptoBytes.aeadEncrypt welcomeKey welcomeNonce BytesLike.empty groupInfoBytes
  mkMlsBytes encryptedWelcomeGroupInfo "encrypt_group_info" "encrypted_welcome_group_info"

/--
Port of `encrypt_welcome`.
MLS* requires `rand: randomness bytes (encrypt_welcome_entropy_length key_packages)`;
otherwise, this function fails when there is not enough randomness.
-/
public
def encryptWelcome (groupInfo: GroupInfo Bytes) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (keyPackages: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes)) (rand: Randomness Bytes)
  : Result (Welcome Bytes)
:= do
  let encryptedGroupInfo ← encryptGroupInfo joinerSecret psks groupInfo
  let groupSecrets ← encryptGroupSecrets encryptedGroupInfo.val joinerSecret (psks.map Prod.fst) keyPackages rand
  let groupSecrets ← mkMlsList groupSecrets "encrypt_welcome" "group_secrets"
  let cipherSuite := availableCiphersuiteToNetwork (CryptoBytes.ciphersuite Bytes)
  pure {
    cipherSuite
    secrets := groupSecrets
    encryptedGroupInfo
  }

/-! ## Utility functions -/

/-- Port of `sign_welcome_group_info`. -/
public
def signWelcomeGroupInfo (signSk: Bytes) (giTbs: GroupInfoTBS Bytes) (rand: Bytes): Result (GroupInfo Bytes) := do
  let tbsBytes := serializeNE GroupInfoTBS.mf giTbs
  let signature ← signWithLabel signSk "GroupInfoTBS" tbsBytes rand
  let signature ← mkMlsBytes signature "sign_welcome_group_info" "signature"
  pure { tbs := giTbs, signature }

end CryptoBytes

/--
Port of `get_signer_verification_key`.
MLS* requires the tree to be at position `0` (`treesync bytes tkt l 0`).
-/
public
def getSignerVerificationKey {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes} {l: Nat}
  (t: TreeSync Bytes tkt l) (groupInfo: GroupInfo Bytes): Result Bytes
:=
  if !(groupInfo.tbs.signer.toNat < 2^l) then
    Result.error "get_signer_verification_key: signer too big"
  else
    match leafAt t groupInfo.tbs.signer.toNat with
    | none => Result.error "get_signer_verification_key: signer is a blank leaf"
    | some ln => pure ln.data.signatureKey.val

/-- Port of `verify_welcome_group_info`. -/
public
def verifyWelcomeGroupInfo {Bytes: Type} [CryptoBytes Bytes] (signPk: Bytes) (gi: GroupInfo Bytes): Bool :=
  let tbsBytes := serializeNE GroupInfoTBS.mf gi.tbs
  verifyWithLabel signPk "GroupInfoTBS" tbsBytes gi.signature.val

end MLS.Bootstrap
