import Mls.NetworkTypes
import Mls.Crypto.Builtins

/-!
Port of `MLS.Crypto.Derived`.

Port-specific differences:
- Labels are plain `String`s: the refinement `valid_label` (ASCII, short enough)
  is checked at runtime by `getMlsLabel`.
- Formats are written by hand, as in `Mls.NetworkTypes`.
-/

namespace Mls

open Comparse

variable {Bytes: Type} [CryptoBytes Bytes]

def availableCiphersuiteFromNetwork: CipherSuite → Result AvailableCiphersuite
  | .mls_128_dhkemx25519_aes128gcm_sha256_ed25519 => pure .mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | .mls_128_dhkemp256_aes128gcm_sha256_p256 => pure .mls_128_dhkemp256_aes128gcm_sha256_p256
  | .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 => pure .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | .mls_256_dhkemx448_aes256gcm_sha512_ed448 => pure .mls_256_dhkemx448_aes256gcm_sha512_ed448
  | .mls_256_dhkemp521_aes256gcm_sha512_p521 => pure .mls_256_dhkemp521_aes256gcm_sha512_p521
  | .mls_256_dhkemx448_chacha20poly1305_sha512_ed448 => pure .mls_256_dhkemx448_chacha20poly1305_sha512_ed448
  | .mls_256_dhkemp384_aes256gcm_sha384_p384 => pure .mls_256_dhkemp384_aes256gcm_sha384_p384
  | .reserved | .unknown .. => Result.error "available_ciphersuite_from_network: ciphersuite not available"

def availableCiphersuiteToNetwork: AvailableCiphersuite → CipherSuite
  | .mls_128_dhkemx25519_aes128gcm_sha256_ed25519 => .mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | .mls_128_dhkemp256_aes128gcm_sha256_p256 => .mls_128_dhkemp256_aes128gcm_sha256_p256
  | .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 => .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | .mls_256_dhkemx448_aes256gcm_sha512_ed448 => .mls_256_dhkemx448_aes256gcm_sha512_ed448
  | .mls_256_dhkemp521_aes256gcm_sha512_p521 => .mls_256_dhkemp521_aes256gcm_sha512_p521
  | .mls_256_dhkemx448_chacha20poly1305_sha512_ed448 => .mls_256_dhkemx448_chacha20poly1305_sha512_ed448
  | .mls_256_dhkemp384_aes256gcm_sha384_p384 => .mls_256_dhkemp384_aes256gcm_sha384_p384

theorem availableCiphersuiteFromNetwork_toNetwork (cs: AvailableCiphersuite):
  availableCiphersuiteFromNetwork (availableCiphersuiteToNetwork cs) = pure cs
:= by
  cases cs <;> rfl

/-! ## Helper functions with refined types -/

def mkMlsBytes {Bytes: Type} [BytesLike Bytes] (b: Bytes) (funName varName: String): Result (MlsBytes Bytes) :=
  if h: mlsNatPred (BytesLike.length b) then
    pure ⟨b, h⟩
  else
    Result.error s!"{funName}: {varName} too long"

def mkMlsAsciiString {Bytes: Type} [BytesLike Bytes] (s: String) (funName varName: String): Result (MlsAsciiString (Bytes := Bytes)) :=
  if h: isAsciiString s then
    let s: Subtype isAsciiString := ⟨s, h⟩
    if h': mlsNatPred (BytesLike.length ((ExtensibleMessageFormat.subtype (Bytes := Bytes) .string isAsciiString).serialize s)) then
      pure ⟨s, h'⟩
    else
      Result.error s!"{funName}: {varName} too long"
  else
    Result.error s!"{funName}: {varName} is not ASCII"

def mkUInt16 (n: Nat) (funName varName: String): Result UInt16 :=
  if n < 2^16 then pure n.toUInt16 else Result.error s!"{funName}: {varName} too big"

def mkUInt32 (n: Nat) (funName varName: String): Result UInt32 :=
  if n < 2^32 then pure n.toUInt32 else Result.error s!"{funName}: {varName} too big"

def serializeNE {Bytes: Type} [BytesLike Bytes] {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (x: α): Bytes :=
  mf.toExtensible.serialize x

/-! ## SignWithLabel / VerifyWithLabel -/

/--
struct {
    opaque label<V>;
    opaque content<V>;
} SignContent;
-/
structure SignContent (Bytes: Type) [BytesLike Bytes] where
  label: MlsAsciiString (Bytes := Bytes)
  content: MlsBytes Bytes

namespace SignContent

def f {Bytes: Type} [BytesLike Bytes]: MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes → SignContent Bytes :=
  fun (label, content) => { label, content }

def g {Bytes: Type} [BytesLike Bytes]: SignContent Bytes → MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes :=
  fun { label, content } => (label, content)

instance {Bytes: Type} [BytesLike Bytes]: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance {Bytes: Type} [BytesLike Bytes]: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end SignContent

def SignContent.mf {Bytes: Type} [BytesLike Bytes]: NonExtensibleMessageFormat Bytes (SignContent Bytes) :=
  .isomorphic (.prod MlsAsciiString.mf MlsBytes.mf) SignContent.f SignContent.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `get_mls_label`. -/
def getMlsLabel {Bytes: Type} [BytesLike Bytes] (label: String): Result (MlsAsciiString (Bytes := Bytes)) :=
  mkMlsAsciiString ("MLS 1.0 " ++ label) "get_mls_label" "label"

def getSignContent (label: String) (content: MlsBytes Bytes): Result Bytes := do
  let label ← getMlsLabel label
  pure (serializeNE SignContent.mf { label, content })

def signWithLabel (signatureKey: Bytes) (label: String) (content: Bytes) (entropy: Bytes): Result Bytes := do
  let content ← mkMlsBytes content "sign_with_label" "content"
  let signContent ← getSignContent label content
  CryptoBytes.signSign signatureKey signContent entropy

def verifyWithLabel (verificationKey: Bytes) (label: String) (content: Bytes) (signature: Bytes): Bool :=
  match (do
    let content ← mkMlsBytes content "verify_with_label" "content"
    getSignContent label content
  : Result Bytes) with
  | .success signContent => CryptoBytes.signVerify verificationKey signContent signature
  | _ => false

/-! ## ExpandWithLabel / DeriveSecret -/

/--
struct {
    uint16 length;
    opaque label<V>;
    opaque context<V>;
} KDFLabel;
-/
structure KdfLabel (Bytes: Type) [BytesLike Bytes] where
  length: UInt16
  label: MlsAsciiString (Bytes := Bytes)
  context: MlsBytes Bytes

namespace KdfLabel

def f {Bytes: Type} [BytesLike Bytes]: UInt16 × MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes → KdfLabel Bytes :=
  fun (length, label, context) => { length, label, context }

def g {Bytes: Type} [BytesLike Bytes]: KdfLabel Bytes → UInt16 × MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes :=
  fun { length, label, context } => (length, label, context)

instance {Bytes: Type} [BytesLike Bytes]: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance {Bytes: Type} [BytesLike Bytes]: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end KdfLabel

def KdfLabel.mf {Bytes: Type} [BytesLike Bytes]: NonExtensibleMessageFormat Bytes (KdfLabel Bytes) :=
  .isomorphic (.prod .uint16BE (.prod MlsAsciiString.mf MlsBytes.mf)) KdfLabel.f KdfLabel.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

def expandWithLabel (secret: Bytes) (label: String) (context: Bytes) (len: Nat): Result Bytes := do
  let length ← mkUInt16 len "expand_with_label" "len"
  let context ← mkMlsBytes context "expand_with_label" "context"
  let label ← getMlsLabel label
  let kdfLabel := serializeNE KdfLabel.mf { length, label, context }
  CryptoBytes.kdfExpand secret kdfLabel len

def deriveSecret (secret: Bytes) (label: String): Result Bytes :=
  expandWithLabel secret label BytesLike.empty (CryptoBytes.kdfLength Bytes)

/-! ## EncryptWithLabel / DecryptWithLabel -/

/--
struct {
  opaque label<V>;
  opaque context<V>;
} EncryptContext;
-/
structure EncryptContext (Bytes: Type) [BytesLike Bytes] where
  label: MlsAsciiString (Bytes := Bytes)
  context: MlsBytes Bytes

namespace EncryptContext

def f {Bytes: Type} [BytesLike Bytes]: MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes → EncryptContext Bytes :=
  fun (label, context) => { label, context }

def g {Bytes: Type} [BytesLike Bytes]: EncryptContext Bytes → MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes :=
  fun { label, context } => (label, context)

instance {Bytes: Type} [BytesLike Bytes]: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance {Bytes: Type} [BytesLike Bytes]: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end EncryptContext

def EncryptContext.mf {Bytes: Type} [BytesLike Bytes]: NonExtensibleMessageFormat Bytes (EncryptContext Bytes) :=
  .isomorphic (.prod MlsAsciiString.mf MlsBytes.mf) EncryptContext.f EncryptContext.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

def computeEncryptionContext (label: String) (context: Bytes): Result Bytes := do
  let context ← mkMlsBytes context "compute_encryption_context" "context"
  let label ← getMlsLabel label
  pure (serializeNE EncryptContext.mf { label, context })

def encryptWithLabel (pkR: Bytes) (label: String) (context: Bytes) (plaintext: Bytes) (entropy: Bytes): Result (Bytes × Bytes) := do
  let contextBytes ← computeEncryptionContext label context
  CryptoBytes.hpkeEncrypt pkR contextBytes BytesLike.empty plaintext entropy

def decryptWithLabel (skR: Bytes) (label: String) (context: Bytes) (kemOutput: Bytes) (ciphertext: Bytes): Result Bytes := do
  let contextBytes ← computeEncryptionContext label context
  CryptoBytes.hpkeDecrypt kemOutput skR contextBytes BytesLike.empty ciphertext

/-! ## Ref hash -/

/--
struct {
  opaque label<V>;
  opaque value<V>;
} RefHashInput;
-/
structure RefHashInput (Bytes: Type) [BytesLike Bytes] where
  label: MlsAsciiString (Bytes := Bytes)
  value: MlsBytes Bytes

namespace RefHashInput

def f {Bytes: Type} [BytesLike Bytes]: MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes → RefHashInput Bytes :=
  fun (label, value) => { label, value }

def g {Bytes: Type} [BytesLike Bytes]: RefHashInput Bytes → MlsAsciiString (Bytes := Bytes) × MlsBytes Bytes :=
  fun { label, value } => (label, value)

instance {Bytes: Type} [BytesLike Bytes]: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance {Bytes: Type} [BytesLike Bytes]: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end RefHashInput

def RefHashInput.mf {Bytes: Type} [BytesLike Bytes]: NonExtensibleMessageFormat Bytes (RefHashInput Bytes) :=
  .isomorphic (.prod MlsAsciiString.mf MlsBytes.mf) RefHashInput.f RefHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Unlike the other labelled functions, the label is used as-is (no "MLS 1.0 " prefix). -/
def refHash (label: String) (value: Bytes): Result Bytes := do
  let label ← mkMlsAsciiString label "ref_hash" "label"
  let value ← mkMlsBytes value "ref_hash" "value"
  let hashContent := serializeNE RefHashInput.mf { label, value }
  CryptoBytes.hashHash hashContent

def makeKeypackageRef (buf: Bytes): Result Bytes :=
  refHash "MLS 1.0 KeyPackage Reference" buf

def makeProposalRef (buf: Bytes): Result Bytes :=
  refHash "MLS 1.0 Proposal Reference" buf

end Mls
