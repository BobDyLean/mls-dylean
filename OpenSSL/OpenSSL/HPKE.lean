import OpenSSL.Hash
import OpenSSL.AEAD

/-!
HPKE (RFC 9180), base mode.

Encryption is deterministic: the ephemeral key pair is derived from caller-provided entropy
with `DeriveKeyPair`.
-/

namespace OpenSSL.HPKE

inductive KEM where
  | dhkemP256HkdfSha256
  | dhkemP384HkdfSha384
  | dhkemP521HkdfSha512
  | dhkemX25519HkdfSha256
  | dhkemX448HkdfSha512
deriving DecidableEq, Repr

/-- RFC 9180 identifier. -/
def KEM.id: KEM → UInt16
  | .dhkemP256HkdfSha256 => 0x0010
  | .dhkemP384HkdfSha384 => 0x0011
  | .dhkemP521HkdfSha512 => 0x0012
  | .dhkemX25519HkdfSha256 => 0x0020
  | .dhkemX448HkdfSha512 => 0x0021

/-- OpenSSL key type of the KEM keys. -/
def KEM.keyType: KEM → String
  | .dhkemP256HkdfSha256 | .dhkemP384HkdfSha384 | .dhkemP521HkdfSha512 => "EC"
  | .dhkemX25519HkdfSha256 => "X25519"
  | .dhkemX448HkdfSha512 => "X448"

/-- OpenSSL curve name (empty for X25519 and X448). -/
def KEM.group: KEM → String
  | .dhkemP256HkdfSha256 => "P-256"
  | .dhkemP384HkdfSha384 => "P-384"
  | .dhkemP521HkdfSha512 => "P-521"
  | .dhkemX25519HkdfSha256 | .dhkemX448HkdfSha512 => ""

/-- `Nsk`: length of a serialized private key. -/
def KEM.privateKeyLength: KEM → Nat
  | .dhkemP256HkdfSha256 => 32
  | .dhkemP384HkdfSha384 => 48
  | .dhkemP521HkdfSha512 => 66
  | .dhkemX25519HkdfSha256 => 32
  | .dhkemX448HkdfSha512 => 56

/-- `Npk` (equal to `Nenc`): length of a serialized public key. -/
def KEM.publicKeyLength: KEM → Nat
  | .dhkemP256HkdfSha256 => 65
  | .dhkemP384HkdfSha384 => 97
  | .dhkemP521HkdfSha512 => 133
  | .dhkemX25519HkdfSha256 => 32
  | .dhkemX448HkdfSha512 => 56

inductive KDF where
  | hkdfSha256
  | hkdfSha384
  | hkdfSha512
deriving DecidableEq, Repr

/-- RFC 9180 identifier. -/
def KDF.id: KDF → UInt16
  | .hkdfSha256 => 0x0001
  | .hkdfSha384 => 0x0002
  | .hkdfSha512 => 0x0003

/-- HKDF over the given hash function. -/
def KDF.ofHash: Hash.Algorithm → KDF
  | .sha2_256 => .hkdfSha256
  | .sha2_384 => .hkdfSha384
  | .sha2_512 => .hkdfSha512

inductive AEAD where
  | aes128Gcm
  | aes256Gcm
  | chacha20Poly1305
deriving DecidableEq, Repr

/-- RFC 9180 identifier. -/
def AEAD.id: AEAD → UInt16
  | .aes128Gcm => 0x0001
  | .aes256Gcm => 0x0002
  | .chacha20Poly1305 => 0x0003

def AEAD.ofAlgorithm: OpenSSL.AEAD.Algorithm → AEAD
  | .aes128Gcm => .aes128Gcm
  | .aes256Gcm => .aes256Gcm
  | .chacha20Poly1305 => .chacha20Poly1305

/-- `Nt`: length of the authentication tag. -/
def AEAD.tagLength (_: AEAD): Nat := 16

structure Ciphersuite where
  kem: KEM
  kdf: KDF
  aead: AEAD
deriving DecidableEq, Repr

@[extern "lean_openssl_hpke_derive_key_pair"]
opaque deriveKeyPairRaw (kem kdf aead: UInt16) (keyType: @& String) (skLen: USize) (ikm: @& ByteArray): Option ByteArray

@[extern "lean_openssl_hpke_seal_base"]
opaque sealBaseRaw (kem kdf aead: UInt16) (pkR info ad plaintext ikmE: @& ByteArray): Option ByteArray

@[extern "lean_openssl_hpke_open_base"]
opaque openBaseRaw (kem kdf aead: UInt16) (keyType group: @& String) (enc skR info ad ciphertext: @& ByteArray): Option ByteArray

/-- `DeriveKeyPair(ikm)`: returns `(sk, pk)`. -/
def deriveKeyPair (cs: Ciphersuite) (ikm: ByteArray): Option (ByteArray × ByteArray) := do
  let skLen := cs.kem.privateKeyLength
  let kp ← deriveKeyPairRaw cs.kem.id cs.kdf.id cs.aead.id cs.kem.keyType skLen.toUSize ikm
  pure (kp.extract 0 skLen, kp.extract skLen kp.size)

/--
`SealBase(pkR, info, aad, pt)`, where the ephemeral key pair is derived from `ikmE` with `DeriveKeyPair`.
Returns `(enc, ciphertext)`.
-/
def sealBase (cs: Ciphersuite) (pkR info ad plaintext ikmE: ByteArray): Option (ByteArray × ByteArray) := do
  let res ← sealBaseRaw cs.kem.id cs.kdf.id cs.aead.id pkR info ad plaintext ikmE
  let encLen := cs.kem.publicKeyLength
  pure (res.extract 0 encLen, res.extract encLen res.size)

/-- `OpenBase(enc, skR, info, aad, ct)`. -/
def openBase (cs: Ciphersuite) (enc skR info ad ciphertext: ByteArray): Option ByteArray :=
  openBaseRaw cs.kem.id cs.kdf.id cs.aead.id cs.kem.keyType cs.kem.group enc skR info ad ciphertext

end OpenSSL.HPKE
