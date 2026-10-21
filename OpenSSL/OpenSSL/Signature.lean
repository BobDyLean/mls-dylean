/-!
Digital signatures.
- EdDSA (RFC 8032), with raw keys.
- ECDSA (FIPS 186-5), with deterministic nonces (RFC 6979), big-endian private scalars,
  uncompressed public points, and DER-encoded signatures.
-/

namespace OpenSSL.Signature

inductive Algorithm where
  | ed25519
  | ed448
  | ecdsaP256Sha256
  | ecdsaP384Sha384
  | ecdsaP521Sha512
deriving DecidableEq, Repr

/-- OpenSSL key type. -/
def Algorithm.keyType: Algorithm → String
  | .ed25519 => "ED25519"
  | .ed448 => "ED448"
  | .ecdsaP256Sha256 | .ecdsaP384Sha384 | .ecdsaP521Sha512 => "EC"

/-- OpenSSL curve name (empty for EdDSA). -/
def Algorithm.group: Algorithm → String
  | .ed25519 | .ed448 => ""
  | .ecdsaP256Sha256 => "P-256"
  | .ecdsaP384Sha384 => "P-384"
  | .ecdsaP521Sha512 => "P-521"

/-- OpenSSL name of the hash function (empty for EdDSA, which hashes internally). -/
def Algorithm.digest: Algorithm → String
  | .ed25519 | .ed448 => ""
  | .ecdsaP256Sha256 => "SHA256"
  | .ecdsaP384Sha384 => "SHA384"
  | .ecdsaP521Sha512 => "SHA512"

def Algorithm.secretKeyLength: Algorithm → Nat
  | .ed25519 => 32
  | .ed448 => 57
  | .ecdsaP256Sha256 => 32
  | .ecdsaP384Sha384 => 48
  | .ecdsaP521Sha512 => 66

def Algorithm.publicKeyLength: Algorithm → Nat
  | .ed25519 => 32
  | .ed448 => 57
  | .ecdsaP256Sha256 => 65
  | .ecdsaP384Sha384 => 97
  | .ecdsaP521Sha512 => 133

@[extern "lean_openssl_secret_to_public"]
opaque secretToPublicRaw (keyType group: @& String) (sk: @& ByteArray): Option ByteArray

@[extern "lean_openssl_sign"]
opaque signRaw (keyType group digest: @& String) (sk msg: @& ByteArray): Option ByteArray

@[extern "lean_openssl_verify"]
opaque verifyRaw (keyType group digest: @& String) (pk msg sig: @& ByteArray): Bool

def secretToPublic (a: Algorithm) (sk: ByteArray): Option ByteArray :=
  secretToPublicRaw a.keyType a.group sk

/-- Deterministic: EdDSA is deterministic by design, ECDSA uses RFC 6979 nonces. -/
def sign (a: Algorithm) (sk msg: ByteArray): Option ByteArray :=
  signRaw a.keyType a.group a.digest sk msg

def verify (a: Algorithm) (pk msg sig: ByteArray): Bool :=
  verifyRaw a.keyType a.group a.digest pk msg sig

end OpenSSL.Signature
