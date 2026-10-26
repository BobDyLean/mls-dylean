module

public import MLS.Common.Code.Crypto.Builtins
public import DY.Comparse
public import DY.EquationalTheory.Hash
public import DySlop.EquationalTheories
public import DySlop.Lib.HPKE
public import DY.Actions.PersistentLocalState
public import DY.Actions.Random

/-!
Port of `MLS.Symbolic`: the `CryptoBytes` instance on symbolic bytes.

Port-specific differences:
- Symbolic bytes are DyLean's `Bytes`, with the DY* equational theories of `DySlop`;
  the instance requires the bytes functor to contain the theories it uses (`HasSymbolicBytes`).
- HPKE is DySlop's port of DY*'s HPKE model; MLS* does not check the length of the KEM output (always 32).
- The lengths left unspecified by MLS* (`magic()`) are 32 (sign entropy), 16 (AEAD key) and 12 (AEAD nonce).
- `hmac_hmac` does not check the length of its output (it is always 32).
- `apply_reuse_guard` (MLS*'s `xor`, admitted in MLS*) fails.
-/

namespace MLS

open DY
open Comparse

/-!
## Configuration

As in DyLean's examples, the instances that symbolic MLS depends on are bundled in typeclasses,
whose fields are scoped instances in the namespace `MLS`:
- `HasSymbolicBytes`: the equational theories used by the symbolic `CryptoBytes` instance,
  and randomness (DyLean's `DY.Random`, for the traceful functions of the symbolic specifications),
- `HasSymbolicInvariants`: the trace types, the cryptographic predicates and the bytes invariants
  used by the symbolic proofs.
The top-level protocol provides them after combining the corresponding instances
(`instance: HasSymbolicBytes where`, `instance: HasSymbolicInvariants where`).
-/

public
class HasSymbolicBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has DY.Literal.SubF]
  [bytesFunc1: BytesFunctor.Has DY.Concat.SubF]
  [bytesFunc2: BytesFunctor.Has DY.Hash.SubF]
  [bytesFunc3: BytesFunctor.Has DySlop.KdfExtract.SubF]
  [bytesFunc4: BytesFunctor.Has DySlop.KdfExpand.SubF]
  [bytesFunc5: BytesFunctor.Has DySlop.Kem.SubF]
  [bytesFunc6: BytesFunctor.Has DySlop.Signature.SubF]
  [bytesFunc7: BytesFunctor.Has DySlop.Aead.SubF]
  [bytesFunc8: BytesFunctor.Has DySlop.Mac.SubF]
  [bytesFunc9: BytesFunctor.Has DY.Random.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has DY.Literal.SubF.length]
  [bytesLen1: BytesLength.Has DY.Concat.SubF.length]
  [bytesLen2: BytesLength.Has DY.Hash.SubF.length]

attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc0
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc1
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc2
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc3
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc4
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc5
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc6
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc7
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc8
attribute [reducible, scoped instance] HasSymbolicBytes.bytesFunc9
attribute [reducible, scoped instance] HasSymbolicBytes.bytesLen
attribute [           scoped instance] HasSymbolicBytes.bytesLen0
attribute [           scoped instance] HasSymbolicBytes.bytesLen1
attribute [           scoped instance] HasSymbolicBytes.bytesLen2

/-- The bundle of HPKE, to use its definitions. -/
public scoped instance [HasSymbolicBytes]: DySlop.HPKE.HasHpkeBytes where

public
class HasSymbolicInvariants extends HasSymbolicBytes where
  [execTraceTypes: ExecTraceTypes]
  [proofTraceTypes: ProofTraceTypes]
  [signPred: DySlop.Signature.SignPred]
  [kdfExpandUsage: DySlop.KdfExpand.KdfExpandUsage]
  [hpkePred: DySlop.HPKE.HpkePred]
  [aeadPred: DySlop.Aead.AeadPred]
  [bytesInv: BytesInvariants]
  [bytesInv0: BytesInvariants.Has DY.Literal.invariants]
  [bytesInv1: BytesInvariants.Has DY.Concat.invariants]
  [bytesInv2: BytesInvariants.Has DySlop.KdfExpand.invariants]
  [bytesInv3: BytesInvariants.Has DySlop.Kem.invariants]
  [bytesInv4: BytesInvariants.Has DySlop.Signature.invariants]
  [bytesInv5: BytesInvariants.Has DySlop.Aead.invariants]

attribute [reducible, scoped instance] HasSymbolicInvariants.execTraceTypes
attribute [reducible, scoped instance] HasSymbolicInvariants.proofTraceTypes
attribute [reducible, scoped instance] HasSymbolicInvariants.signPred
attribute [reducible, scoped instance] HasSymbolicInvariants.kdfExpandUsage
attribute [reducible, scoped instance] HasSymbolicInvariants.hpkePred
attribute [reducible, scoped instance] HasSymbolicInvariants.aeadPred
attribute [reducible, scoped instance] HasSymbolicInvariants.bytesInv
attribute [           scoped instance] HasSymbolicInvariants.bytesInv0
attribute [           scoped instance] HasSymbolicInvariants.bytesInv1
attribute [           scoped instance] HasSymbolicInvariants.bytesInv2
attribute [           scoped instance] HasSymbolicInvariants.bytesInv3
attribute [           scoped instance] HasSymbolicInvariants.bytesInv4
attribute [           scoped instance] HasSymbolicInvariants.bytesInv5

/-- The bundle of HPKE, to use its theorems. -/
public scoped instance [HasSymbolicInvariants]: DySlop.HPKE.HasHpkeInvariants where

/-! ## Typeclass instantiation on DY* -/

variable [HasSymbolicBytes]

/-- Port of `bytes_has_crypto_bytes`, for the ciphersuite of `crypto_bytes_bytes`. -/
public
instance cryptoBytesBytes: CryptoBytes Bytes where
  toBytesLike := inferInstance
  ciphersuite := .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

  hashHash buf := pure (DY.Hash.hash buf)
  hashHash_ne_empty buf := by
    intro h
    have := congrArg BytesLike.length (Result.success.inj h)
    simp [BytesLike.length, BytesLike.empty, DY.Hash.length_hash, DY.Hash.hashLength_neq_0] at this
  hashOutputLength := 32

  kdfLength := 32
  kdfExtract salt ikm := pure (DySlop.KdfExtract.kdfExtract salt ikm)
  kdfExpand prk info len :=
    if len = 0 then
      Result.internalFailure "kdf_expand: len cannot be zero"
    else
      pure (DySlop.KdfExpand.kdfExpand prk info len)

  hpkePublicKeyLength := 32
  hpkePrivateKeyLength := 32
  hpkeKemOutputLength := 32
  hpkeGenKeypair ikm :=
    if BytesLike.length ikm ≠ 32 then
      Result.error "hpke_gen_keypair: ikm too big"
    else
      pure (ikm, DySlop.HPKE.hpkePk ikm)
  hpkeEncrypt pkR info ad plaintext entropy := pure (DySlop.HPKE.hpkeEnc pkR entropy plaintext info ad)
  hpkeDecrypt enc skR info ad ciphertext :=
    match DySlop.HPKE.hpkeDec skR (enc, ciphertext) info ad with
    | some plaintext => pure plaintext
    | none => Result.error "hpke_decrypt failed"

  signGenKeypairMinEntropyLength := 32
  signGenKeypair entropy := pure (DySlop.Signature.vk entropy, entropy)
  signSignMinEntropyLength := 32
  signSign signatureKey buf entropy := pure (DySlop.Signature.sign signatureKey entropy buf)
  signVerify verificationKey buf signature := DySlop.Signature.verify verificationKey buf signature

  aeadNonceLength := 12
  aeadKeyLength := 16
  aeadEncrypt key nonce ad plaintext := pure (DySlop.Aead.aeadEnc key nonce plaintext ad)
  aeadDecrypt key nonce ad ciphertext :=
    match DySlop.Aead.aeadDec key nonce ciphertext ad with
    | some res => pure res
    | none => Result.error "aead_decrypt: couldn't decrypt"

  hmacLength := 32
  hmacHmac key data := pure (DySlop.Mac.macCompute key data)

  stringToBytes s := BytesLike.fromByteArray s.toUTF8
  applyReuseGuard _ _ := Result.internalFailure "apply_reuse_guard: not supported on symbolic bytes"

@[simp]
public
theorem cryptoBytesBytes_signSign (signatureKey buf entropy: Bytes):
  CryptoBytes.signSign signatureKey buf entropy = .success (DySlop.Signature.sign signatureKey entropy buf)
:= rfl

@[simp]
public
theorem cryptoBytesBytes_kdfExpand (prk info: Bytes) (len: Nat):
  CryptoBytes.kdfExpand prk info len =
    if len = 0 then Result.internalFailure "kdf_expand: len cannot be zero" else .success (DySlop.KdfExpand.kdfExpand prk info len)
:= rfl

@[simp]
public
theorem cryptoBytesBytes_hpkeEncrypt (pkR info ad plaintext entropy: Bytes):
  CryptoBytes.hpkeEncrypt pkR info ad plaintext entropy = .success (DySlop.HPKE.hpkeEnc pkR entropy plaintext info ad)
:= rfl

@[simp]
public
theorem cryptoBytesBytes_hpkeDecrypt (enc skR info ad ciphertext: Bytes):
  CryptoBytes.hpkeDecrypt enc skR info ad ciphertext = (
    match DySlop.HPKE.hpkeDec skR (enc, ciphertext) info ad with
    | some plaintext => .success plaintext
    | none => Result.error "hpke_decrypt failed")
:= rfl

@[simp]
public
theorem cryptoBytesBytes_signVerify (verificationKey buf signature: Bytes):
  CryptoBytes.signVerify verificationKey buf signature = DySlop.Signature.verify verificationKey buf signature
:= rfl

/--
  Port of `mk_mls_sigkey_usage`.
  The principal is encoded as a literal (MLS* serializes the structure `mls_principal`, containing only the principal).
-/
@[expose]
public
def mkMlsSigkeyUsage (who: Participant): Usage :=
  Usage.sigKey "MLS.LeafSignKey" (DY.Literal.literalToBytes who.toUTF8)

/-- Port of `extract_result`. -/
public
def extractResult [ExecTraceTypes] {α: Type} (x: Result α): Traceful α :=
  match x with
  | .success y => pure y
  | _ => failure

end MLS
