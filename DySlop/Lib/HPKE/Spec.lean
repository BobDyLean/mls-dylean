/-
  Port of `DY.Lib.HPKE.Spec`: the specification of HPKE
  (the single-shot API in base mode, c.f. section 6.1 of RFC 9180).

  As in DY*, this specification is not compliant with RFC 9180:
  the message formatting differs (e.g. the one in LabeledExpand),
  and some KDF.Extract were omitted (`info` and `shared_secret` are not extracted).
-/

module

public import DY.Comparse
public import DySlop.EquationalTheories

open DY DY.Comparse

namespace DySlop.HPKE

/-!
## Configuration

As in DyLean's examples, the instances HPKE depends on are bundled in typeclasses,
whose fields are scoped instances in the namespace `DySlop.HPKE`:
- `HasHpkeBytes`: the equational theories used by HPKE,
- `HasHpkeInvariants` (in `DySlop.Lib.HPKE.Lemmas`): the predicates and bytes invariants used by the HPKE theorems.
The types (`LabeledExpandInfo`, `HpkePred`, …) only depend on `[BytesFunctor]` (and the trace types).
A protocol provides the bundles after combining the corresponding instances
(`instance: HasHpkeBytes where`, `instance: HasHpkeInvariants where`);
a library using HPKE can extend them in its own bundles.
-/

public
class HasHpkeBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has DY.Literal.SubF]
  [bytesFunc1: BytesFunctor.Has DY.Concat.SubF]
  [bytesFunc2: BytesFunctor.Has DySlop.Kem.SubF]
  [bytesFunc3: BytesFunctor.Has DySlop.KdfExpand.SubF]
  [bytesFunc4: BytesFunctor.Has DySlop.Aead.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has DY.Literal.SubF.length]
  [bytesLen1: BytesLength.Has DY.Concat.SubF.length]

attribute [reducible, scoped instance] HasHpkeBytes.bytesFunc
attribute [reducible, scoped instance] HasHpkeBytes.bytesFunc0
attribute [reducible, scoped instance] HasHpkeBytes.bytesFunc1
attribute [reducible, scoped instance] HasHpkeBytes.bytesFunc2
attribute [reducible, scoped instance] HasHpkeBytes.bytesFunc3
attribute [reducible, scoped instance] HasHpkeBytes.bytesFunc4
attribute [reducible, scoped instance] HasHpkeBytes.bytesLen
attribute [           scoped instance] HasHpkeBytes.bytesLen0
attribute [           scoped instance] HasHpkeBytes.bytesLen1

section Types

variable [BytesFunctor]

/--
  Port of `hpke_labeled_expand_info`, the `labeled_info` of LabeledExpand:
  `labeled_info = concat(I2OSP(L, 2), "HPKE-v1", suite_id, label, info)`.
  As in DY*, the format is not compliant with the RFC, but is non-ambiguous.
-/
public
structure LabeledExpandInfo where
  len: UInt16
  /-- "label" as in HPKE's LabeledExpand, not as in security labels. -/
  label: String
  info: Bytes

end Types

variable [HasHpkeBytes]

public
instance LabeledExpandInfo.ps: ParseableSerializeable LabeledExpandInfo := .make <|
  .triviallyIsomorphic (.prod .uint16 (.prod .slowString .bytes))
    (fun ⟨len, label, info⟩ => { len, label, info })
    (fun { len, label, info } => ⟨len, label, info⟩)

/--
  Port of `hpke_labeled_expand`:
  `LabeledExpand(prk, label, info, L) = Expand(prk, labeled_info, L)`.
  DY* requires `len <> 0`.
-/
public
def labeledExpand (prk: Bytes) (label: String) (info: Bytes) (len: UInt16): Bytes :=
  DySlop.KdfExpand.kdfExpand prk (serialize ({ len, label, info }: LabeledExpandInfo)) len.toNat

/-- Port of `hpke_pk`. -/
@[expose]
public
def hpkePk (sk: Bytes): Bytes :=
  DySlop.Kem.kemPk sk

/-- Port of `hpke_enc`. -/
public
def hpkeEnc (pkR entropy plaintext info ad: Bytes): Bytes × Bytes :=
  let (enc, sharedSecret) := DySlop.Kem.kemEncap pkR entropy
  let aeadKey := labeledExpand sharedSecret "key" info 32
  let aeadNonce := labeledExpand sharedSecret "base_nonce" info 32
  let cipher := DySlop.Aead.aeadEnc aeadKey aeadNonce plaintext ad
  (enc, cipher)

/-- Port of `hpke_dec`. -/
public
def hpkeDec (skR: Bytes) (encCiphertext: Bytes × Bytes) (info ad: Bytes): Option Bytes :=
  match DySlop.Kem.kemDecap skR encCiphertext.1 with
  | none => none
  | some sharedSecret =>
    let aeadKey := labeledExpand sharedSecret "key" info 32
    let aeadNonce := labeledExpand sharedSecret "base_nonce" info 32
    DySlop.Aead.aeadDec aeadKey aeadNonce encCiphertext.2 ad

/-- Port of `hpke_dec_enc` (sanity check). -/
public
theorem hpke_dec_enc (skR entropy plaintext info ad: Bytes)
  : hpkeDec skR (hpkeEnc (hpkePk skR) entropy plaintext info ad) info ad = some plaintext
:= by
  simp only [hpkeDec, hpkeEnc, hpkePk, DySlop.Kem.kem_decap_encap, DySlop.Aead.aead_dec_enc]

end DySlop.HPKE
