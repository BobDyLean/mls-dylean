import Mls.Comparse.Bytes
import Mls.Common.Code.Result
import OpenSSL

/-!
Port of `MLS.Crypto.Builtins`.

Port-specific differences:
- The concrete instance uses the OpenSSL bindings of `OpenSSL/` instead of HACL*'s specifications.
- `concrete_ciphersuite`'s pair `(kem_dh, kem_hash)` is represented by the HPKE KEM.
  It is not meant to be secure, and is used for testing.
- `AvailableCiphersuite` contains all the cipher suites of RFC 9420, not only the two supported by HACL*.
- ECDSA signatures use deterministic nonces (RFC 6979), so `sign_sign` ignores its entropy (as for EdDSA).
- The fields of `crypto_bytes` that only carry proofs (e.g. `hash_hash_pre`, `*_length_bound`)
  are not ported yet, as well as `debug_bytes_to_string`.
- `bytes_hasEq` is `DecidableEq Bytes`.
- Refined types such as `lbytes bytes n` are not used in the signatures of `CryptoBytes`:
  lengths are checked at runtime by the concrete instance.
-/

namespace Mls

open Comparse

/-! ## Typeclass definition -/

/-- All the cipher suites of RFC 9420 (MLS* only supports the first and third ones). -/
inductive AvailableCiphersuite where
  | mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | mls_128_dhkemp256_aes128gcm_sha256_p256
  | mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | mls_256_dhkemx448_aes256gcm_sha512_ed448
  | mls_256_dhkemp521_aes256gcm_sha512_p521
  | mls_256_dhkemx448_chacha20poly1305_sha512_ed448
  | mls_256_dhkemp384_aes256gcm_sha384_p384
deriving DecidableEq, Repr

class CryptoBytes (Bytes: Type) extends BytesLike Bytes where
  /-- Port of `bytes_hasEq`. -/
  [decEq: DecidableEq Bytes]

  ciphersuite: AvailableCiphersuite

  hashHash: Bytes → Result Bytes
  hashOutputLength: Nat

  kdfLength: Nat
  kdfExtract: (key: Bytes) → (data: Bytes) → Result Bytes
  kdfExpand: (prk: Bytes) → (info: Bytes) → (len: Nat) → Result Bytes

  hpkePublicKeyLength: Nat
  hpkePrivateKeyLength: Nat
  hpkeKemOutputLength: Nat
  hpkeGenKeypair: (ikm: Bytes) → Result (Bytes × Bytes)
  hpkeEncrypt: (pkR: Bytes) → (info: Bytes) → (ad: Bytes) → (plaintext: Bytes) → (entropy: Bytes) → Result (Bytes × Bytes)
  hpkeDecrypt: (enc: Bytes) → (skR: Bytes) → (info: Bytes) → (ad: Bytes) → (ciphertext: Bytes) → Result Bytes

  signGenKeypairMinEntropyLength: Nat
  signGenKeypair: (entropy: Bytes) → Result (Bytes × Bytes)
  signSignMinEntropyLength: Nat
  signSign: (signatureKey: Bytes) → (buf: Bytes) → (entropy: Bytes) → Result Bytes
  signVerify: (verificationKey: Bytes) → (buf: Bytes) → (signature: Bytes) → Bool

  aeadNonceLength: Nat
  aeadKeyLength: Nat
  aeadEncrypt: (key: Bytes) → (nonce: Bytes) → (ad: Bytes) → (plaintext: Bytes) → Result Bytes
  aeadDecrypt: (key: Bytes) → (nonce: Bytes) → (ad: Bytes) → (ciphertext: Bytes) → Result Bytes

  hmacLength: Nat
  hmacHmac: (key: Bytes) → (data: Bytes) → Result Bytes

  stringToBytes: String → Bytes

attribute [reducible, instance] CryptoBytes.decEq

/-! ## Concrete instance -/

open OpenSSL

/--
Port of `concrete_ciphersuite`.
The pair `(kem_dh, kem_hash)` of MLS* is represented by the HPKE KEM.
-/
structure ConcreteCiphersuite where
  kem: HPKE.KEM
  aead: AEAD.Algorithm
  kdfHash: Hash.Algorithm

/-- Port of `concrete_ciphersuite_to_hpke_ciphersuite`. -/
def concreteCiphersuiteToHpkeCiphersuite (cs: ConcreteCiphersuite): HPKE.Ciphersuite :=
  { kem := cs.kem, kdf := .ofHash cs.kdfHash, aead := .ofAlgorithm cs.aead }

/-- Port of `signature_functions` (copy-pasted from `CryptoBytes`, specialized to `ByteArray`). -/
structure SignatureFunctions where
  signGenKeypairMinEntropyLength: Nat
  signGenKeypair: (entropy: ByteArray) → Result (ByteArray × ByteArray)
  signSignMinEntropyLength: Nat
  signSign: (signatureKey: ByteArray) → (buf: ByteArray) → (entropy: ByteArray) → Result ByteArray
  signVerify: (verificationKey: ByteArray) → (buf: ByteArray) → (signature: ByteArray) → Bool

/--
Port of `signature_functions`.
Generalization of `ed25519_signature_functions` to all the signature algorithms.
Signing is deterministic (ECDSA uses RFC 6979 nonces), hence ignores its entropy.
-/
def signatureFunctions (a: Signature.Algorithm): SignatureFunctions where
  signGenKeypairMinEntropyLength := a.secretKeyLength
  signGenKeypair rand := do
    let randSlice := rand.extract 0 a.secretKeyLength
    let pk ← Result.fromOption "sign_gen_keypair: secret_to_public failed" (Signature.secretToPublic a randSlice)
    pure (pk, randSlice)
  signSignMinEntropyLength := 0
  signSign sk msg _ :=
    if sk.size != a.secretKeyLength then
      Result.error "sign_sign: bad signature key size"
    else
      Result.fromOption "sign_sign: sign failed" (Signature.sign a sk msg)
  signVerify pk msg signature :=
    Signature.verify a pk msg signature

/-- Port of `available_ciphersuite_to_concrete_ciphersuite`. -/
def availableCiphersuiteToConcreteCiphersuite: AvailableCiphersuite → ConcreteCiphersuite × SignatureFunctions
  | .mls_128_dhkemx25519_aes128gcm_sha256_ed25519 =>
    ({ kem := .dhkemX25519HkdfSha256, aead := .aes128Gcm, kdfHash := .sha2_256 }, signatureFunctions .ed25519)
  | .mls_128_dhkemp256_aes128gcm_sha256_p256 =>
    ({ kem := .dhkemP256HkdfSha256, aead := .aes128Gcm, kdfHash := .sha2_256 }, signatureFunctions .ecdsaP256Sha256)
  | .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 =>
    ({ kem := .dhkemX25519HkdfSha256, aead := .chacha20Poly1305, kdfHash := .sha2_256 }, signatureFunctions .ed25519)
  | .mls_256_dhkemx448_aes256gcm_sha512_ed448 =>
    ({ kem := .dhkemX448HkdfSha512, aead := .aes256Gcm, kdfHash := .sha2_512 }, signatureFunctions .ed448)
  | .mls_256_dhkemp521_aes256gcm_sha512_p521 =>
    ({ kem := .dhkemP521HkdfSha512, aead := .aes256Gcm, kdfHash := .sha2_512 }, signatureFunctions .ecdsaP521Sha512)
  | .mls_256_dhkemx448_chacha20poly1305_sha512_ed448 =>
    ({ kem := .dhkemX448HkdfSha512, aead := .chacha20Poly1305, kdfHash := .sha2_512 }, signatureFunctions .ed448)
  | .mls_256_dhkemp384_aes256gcm_sha384_p384 =>
    ({ kem := .dhkemP384HkdfSha384, aead := .aes256Gcm, kdfHash := .sha2_384 }, signatureFunctions .ecdsaP384Sha384)

/-- Port of `mk_concrete_crypto_bytes`. -/
@[instance_reducible]
def mkConcreteCryptoBytes (acs: AvailableCiphersuite): CryptoBytes ByteArray :=
  let (cs, sign) := availableCiphersuiteToConcreteCiphersuite acs
  let hpkeCs := concreteCiphersuiteToHpkeCiphersuite cs
  {
    -- As MLS*'s postcondition `cb.base == bytes_like_hacl_star_bytes`, which holds here by definition.
    toBytesLike := bytesLikeByteArray

    ciphersuite := acs

    hashHash buf := Result.fromOption "hash_hash: Hash.hash failed" (Hash.hash cs.kdfHash buf)
    hashOutputLength := cs.kdfHash.hashLength

    kdfLength := cs.kdfHash.hashLength
    kdfExtract key data :=
      Result.fromOption "kdf_extract: HKDF.extract failed" (Hash.hkdfExtract cs.kdfHash key data)
    kdfExpand prk info len :=
      if prk.size < cs.kdfHash.hashLength then
        Result.internalFailure "kdf_expand: prk too small"
      else if 255 * cs.kdfHash.hashLength < len then
        Result.internalFailure "kdf_expand: len too high"
      else
        Result.fromOption "kdf_expand: HKDF.expand failed" (Hash.hkdfExpand cs.kdfHash prk info len)

    hpkePublicKeyLength := cs.kem.publicKeyLength
    hpkePrivateKeyLength := cs.kem.privateKeyLength
    hpkeKemOutputLength := cs.kem.publicKeyLength
    hpkeGenKeypair ikm :=
      Result.fromOption "hpke_gen_keypair: HPKE.derive_key_pair failed" (HPKE.deriveKeyPair hpkeCs ikm)
    hpkeEncrypt pkR info ad plaintext rand :=
      if pkR.size != cs.kem.publicKeyLength then
        Result.internalFailure "hpke_encrypt: bad public key length"
      else
        Result.fromOption "hpke_encrypt: HPKE.sealBase failed" (HPKE.sealBase hpkeCs pkR info ad plaintext rand)
    hpkeDecrypt enc skR info ad ciphertext :=
      if ciphertext.size < cs.aead.tagLength then
        Result.error "hpke_decrypt: ciphertext too short"
      else
        Result.fromOption "hpke_decrypt: HPKE.openBase failed" (HPKE.openBase hpkeCs enc skR info ad ciphertext)

    signGenKeypairMinEntropyLength := sign.signGenKeypairMinEntropyLength
    signGenKeypair := sign.signGenKeypair
    signSignMinEntropyLength := sign.signSignMinEntropyLength
    signSign := sign.signSign
    signVerify := sign.signVerify

    aeadNonceLength := cs.aead.nonceLength
    aeadKeyLength := cs.aead.keyLength
    aeadEncrypt key nonce ad plaintext :=
      Result.fromOption "aead_encrypt: AEAD.encrypt failed" (AEAD.encrypt cs.aead key nonce ad plaintext)
    aeadDecrypt key nonce ad ciphertext :=
      if ciphertext.size < cs.aead.tagLength then
        Result.error "aead_decrypt: ciphertext too short"
      else
        Result.fromOption "aead_decrypt: AEAD.decrypt failed" (AEAD.decrypt cs.aead key nonce ad ciphertext)

    hmacLength := cs.kdfHash.hashLength
    hmacHmac key data := Result.fromOption "hmac_hmac: HMAC.hmac failed" (Hash.hmac cs.kdfHash key data)

    stringToBytes s := s.toUTF8
  }

end Mls
