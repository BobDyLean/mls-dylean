module

public import MLS.Comparse.Derived
import all Comparse.Formats.Basic

/-!
Port of `MLS.NetworkTypes`.

Port-specific differences:
- `nat_lbytes 1`, `nat_lbytes 2`, `nat_lbytes 4`, `nat_lbytes 8` are represented with
  `UInt8`, `UInt16`, `UInt32` and `UInt64`, serialized in big-endian
  (`uint8`, `uint16BE`, `uint32BE`, `uint64BE`; DyLean's `uint16`, `uint32`, `uint64` are little-endian).
- Closed enumerations whose tags start at 1 use `subsetIsomorphic` on the raw integer;
  tagged unions with invalid tags (e.g. `reserved`) map them to `Empty`.
- Open enumerations (`open_tag`) are represented with an `unknown` constructor
  carrying the raw integer, refined to be different from the known tags.
- `mls_list bytes ps_a` is represented with `MlsList mf`, refined on the length of the serialization
  (as `pre_length_list` in Comparse).
- The message formats and their non-ambiguity / unique representation proofs
  are written by hand, the Comparse (F*) metaprogram is not available.
-/

namespace MLS

open Comparse

variable {Bytes: Type} [BytesLike Bytes]

/-! ## MLS variable-length integers, bytes and lists -/

@[expose]
public
def mlsNatPred (n: Nat): Prop := n < 2^30

public
instance: DecidablePred mlsNatPred := fun n => inferInstanceAs (Decidable (n < 2^30))

public
abbrev MlsNat := {n: Nat // mlsNatPred n}

@[expose]
public
def MlsNat.f (n: {n: QuicNat // mlsNatPred n.val}): MlsNat := ⟨n.val.val, n.property⟩
@[expose]
public
def MlsNat.g (n: MlsNat): {n: QuicNat // mlsNatPred n.val} :=
  ⟨⟨n.val, by grind [mlsNatPred]⟩, n.property⟩

public
instance: LeftInverse MlsNat.g MlsNat.f := ⟨by intro _; rfl⟩
public
instance: RightInverse MlsNat.g MlsNat.f := ⟨by intro _; rfl⟩

@[expose]
public
def MlsNat.mf: NonExtensibleMessageFormat Bytes MlsNat :=
  .isomorphic (.subtype .quicNat (fun n => mlsNatPred n.val)) MlsNat.f MlsNat.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- MLS integers contain no bytes (their well-formedness is trivial). -/
@[simp]
public
theorem MlsNat.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: MlsNat):
  (MlsNat.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [MlsNat.mf]

public
abbrev MlsBytes (Bytes: Type) [BytesLike Bytes] := {b: Bytes // mlsNatPred (BytesLike.length b)}

/-- The empty `MlsBytes`. -/
@[expose]
public
def MlsBytes.empty: MlsBytes Bytes :=
  ⟨BytesLike.empty, by simp [mlsNatPred, BytesLike.empty_length]⟩

public
def MlsBytes.mf: NonExtensibleMessageFormat Bytes (MlsBytes Bytes) :=
  .lengthPrefix mlsNatPred MlsNat.mf .bytes

namespace MlsBytes.mf

public
instance: (MlsBytes.mf (Bytes := Bytes)).IsNonAmbiguous := by
  dsimp only [MlsBytes.mf]
  exact inferInstanceAs (NonExtensibleMessageFormat.lengthPrefix mlsNatPred MlsNat.mf .bytes).IsNonAmbiguous

public
instance: (MlsBytes.mf (Bytes := Bytes)).HasUniqueRepresentation := by
  dsimp only [MlsBytes.mf]
  exact inferInstanceAs (NonExtensibleMessageFormat.lengthPrefix mlsNatPred MlsNat.mf .bytes).HasUniqueRepresentation

public
instance: (MlsBytes.mf (Bytes := Bytes)).ParseConsumes := by
  dsimp only [MlsBytes.mf]
  exact inferInstanceAs (NonExtensibleMessageFormat.lengthPrefix mlsNatPred MlsNat.mf .bytes).ParseConsumes

@[simp]
public
theorem wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: MlsBytes Bytes):
  (MlsBytes.mf (Bytes := Bytes)).wf pred x = pred x.val
:=
  (NonExtensibleMessageFormat.lengthPrefix.wf_eq mlsNatPred MlsNat.mf .bytes pred x).trans (by simp [MlsNat.mf])

end MlsBytes.mf

public
abbrev MlsList
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
:=
  {l: List a // mlsNatPred (BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l))}

@[expose]
public
def MlsList.mf
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
  : NonExtensibleMessageFormat Bytes (MlsList mf)
:=
  .lengthPrefix mlsNatPred MlsNat.mf (.list mf)

namespace MlsList.mf

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] [mf.IsNonAmbiguous]
  : (MlsList.mf mf).IsNonAmbiguous
:= by
  dsimp only [MlsList.mf]
  infer_instance

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] [mf.HasUniqueRepresentation]
  : (MlsList.mf mf).HasUniqueRepresentation
:= by
  dsimp only [MlsList.mf]
  infer_instance

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
  : (MlsList.mf mf).ParseConsumes
:= by
  dsimp only [MlsList.mf]
  infer_instance

@[simp]
public
theorem wf_eq
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: MlsList mf)
  : (MlsList.mf mf).wf pred x = ∀ y ∈ x.val, mf.wf pred y
:= by
  simp [MlsList.mf]

end MlsList.mf

/-! ## ASCII strings -/

@[expose]
public
def isAsciiString (s: String): Prop := ∀ c ∈ s.toList, c.toNat < 128

public
instance: DecidablePred isAsciiString := fun s =>
  inferInstanceAs (Decidable (∀ c ∈ s.toList, c.toNat < 128))

/--
Port of `mls_ascii_string`.
We encode ASCII strings with their UTF-8 encoding, which coincides with the ASCII encoding.
-/
public
abbrev MlsAsciiString :=
  {s: Subtype isAsciiString // mlsNatPred (BytesLike.length ((ExtensibleMessageFormat.subtype (Bytes := Bytes) .string isAsciiString).serialize s))}

@[expose]
public
def MlsAsciiString.mf: NonExtensibleMessageFormat Bytes (MlsAsciiString (Bytes := Bytes)) :=
  .lengthPrefix mlsNatPred MlsNat.mf (.subtype .string isAsciiString)
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- ASCII strings contain no bytes (their well-formedness is trivial). -/
@[simp]
public
theorem MlsAsciiString.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: MlsAsciiString (Bytes := Bytes)):
  (MlsAsciiString.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [MlsAsciiString.mf, MlsNat.mf]

/-! ## HPKEPublicKey, MAC -/

/-- opaque HPKEPublicKey<V>; -/
public
abbrev HpkePublicKey (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

@[expose]
public
def HpkePublicKey.mf: NonExtensibleMessageFormat Bytes (HpkePublicKey Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem HpkePublicKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: HpkePublicKey Bytes):
  (HpkePublicKey.mf (Bytes := Bytes)).wf pred x = pred x.val
:= by
  simp [HpkePublicKey.mf]

/-- opaque MAC<V>; -/
public
abbrev Mac (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

@[expose]
public
def Mac.mf: NonExtensibleMessageFormat Bytes (Mac Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem Mac.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Mac Bytes):
  (Mac.mf (Bytes := Bytes)).wf pred x = pred x.val
:= by
  simp [Mac.mf]

/-! ## ProtocolVersion -/

/--
enum {
    reserved(0),
    mls10(1),
    (255)
} ProtocolVersion;
-/
public
inductive ProtocolVersion where
  | reserved
  | mls10
  | unknown (n: UInt16) (h: 1 < n.toNat)
deriving DecidableEq

@[expose]
public
def ProtocolVersion.ofUInt16 (n: UInt16): ProtocolVersion :=
  match _: n.toNat with
  | 0 => .reserved
  | 1 => .mls10
  | _+2 => .unknown n (by grind)

@[expose]
public
def ProtocolVersion.toUInt16: ProtocolVersion → UInt16
  | .reserved => 0
  | .mls10 => 1
  | .unknown n _ => n

public
instance: LeftInverse ProtocolVersion.toUInt16 ProtocolVersion.ofUInt16 where
  left_inv n := by grind [ProtocolVersion.ofUInt16, ProtocolVersion.toUInt16]

public
instance: RightInverse ProtocolVersion.toUInt16 ProtocolVersion.ofUInt16 where
  right_inv x := by cases x <;> grind [ProtocolVersion.ofUInt16, ProtocolVersion.toUInt16]

@[expose]
public
def ProtocolVersion.mf: NonExtensibleMessageFormat Bytes ProtocolVersion :=
  .isomorphic .uint16BE ProtocolVersion.ofUInt16 ProtocolVersion.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ProtocolVersion.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ProtocolVersion):
  (ProtocolVersion.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [ProtocolVersion.mf]

/-! ## CipherSuite -/

/-- uint16 CipherSuite; -/
public
inductive CipherSuite where
  | reserved
  | mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | mls_128_dhkemp256_aes128gcm_sha256_p256
  | mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | mls_256_dhkemx448_aes256gcm_sha512_ed448
  | mls_256_dhkemp521_aes256gcm_sha512_p521
  | mls_256_dhkemx448_chacha20poly1305_sha512_ed448
  | mls_256_dhkemp384_aes256gcm_sha384_p384
  | unknown (n: UInt16) (h: 7 < n.toNat)
deriving DecidableEq

@[expose]
public
def CipherSuite.ofUInt16 (n: UInt16): CipherSuite :=
  match _: n.toNat with
  | 0 => .reserved
  | 1 => .mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | 2 => .mls_128_dhkemp256_aes128gcm_sha256_p256
  | 3 => .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | 4 => .mls_256_dhkemx448_aes256gcm_sha512_ed448
  | 5 => .mls_256_dhkemp521_aes256gcm_sha512_p521
  | 6 => .mls_256_dhkemx448_chacha20poly1305_sha512_ed448
  | 7 => .mls_256_dhkemp384_aes256gcm_sha384_p384
  | _+8 => .unknown n (by grind)

@[expose]
public
def CipherSuite.toUInt16: CipherSuite → UInt16
  | .reserved => 0
  | .mls_128_dhkemx25519_aes128gcm_sha256_ed25519 => 1
  | .mls_128_dhkemp256_aes128gcm_sha256_p256 => 2
  | .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 => 3
  | .mls_256_dhkemx448_aes256gcm_sha512_ed448 => 4
  | .mls_256_dhkemp521_aes256gcm_sha512_p521 => 5
  | .mls_256_dhkemx448_chacha20poly1305_sha512_ed448 => 6
  | .mls_256_dhkemp384_aes256gcm_sha384_p384 => 7
  | .unknown n _ => n

public
instance: LeftInverse CipherSuite.toUInt16 CipherSuite.ofUInt16 where
  left_inv n := by grind [CipherSuite.ofUInt16, CipherSuite.toUInt16]

public
instance: RightInverse CipherSuite.toUInt16 CipherSuite.ofUInt16 where
  right_inv x := by cases x <;> grind [CipherSuite.ofUInt16, CipherSuite.toUInt16]

@[expose]
public
def CipherSuite.mf: NonExtensibleMessageFormat Bytes CipherSuite :=
  .isomorphic .uint16BE CipherSuite.ofUInt16 CipherSuite.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem CipherSuite.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: CipherSuite):
  (CipherSuite.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [CipherSuite.mf]

/-! ## ExtensionType -/

/-- uint16 ExtensionType; -/
public
inductive ExtensionType where
  | reserved
  | applicationId
  | ratchetTree
  | requiredCapabilities
  | externalPub
  | externalSenders
  | unknown (n: UInt16) (h: 5 < n.toNat)
deriving DecidableEq

@[expose]
public
def ExtensionType.ofUInt16 (n: UInt16): ExtensionType :=
  match _: n.toNat with
  | 0 => .reserved
  | 1 => .applicationId
  | 2 => .ratchetTree
  | 3 => .requiredCapabilities
  | 4 => .externalPub
  | 5 => .externalSenders
  | _+6 => .unknown n (by grind)

@[expose]
public
def ExtensionType.toUInt16: ExtensionType → UInt16
  | .reserved => 0
  | .applicationId => 1
  | .ratchetTree => 2
  | .requiredCapabilities => 3
  | .externalPub => 4
  | .externalSenders => 5
  | .unknown n _ => n

public
instance: LeftInverse ExtensionType.toUInt16 ExtensionType.ofUInt16 where
  left_inv n := by grind [ExtensionType.ofUInt16, ExtensionType.toUInt16]

public
instance: RightInverse ExtensionType.toUInt16 ExtensionType.ofUInt16 where
  right_inv x := by cases x <;> grind [ExtensionType.ofUInt16, ExtensionType.toUInt16]

@[expose]
public
def ExtensionType.mf: NonExtensibleMessageFormat Bytes ExtensionType :=
  .isomorphic .uint16BE ExtensionType.ofUInt16 ExtensionType.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ExtensionType.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ExtensionType):
  (ExtensionType.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [ExtensionType.mf]

/-! ## Extension -/

/--
struct {
    ExtensionType extension_type;
    opaque extension_data<V>;
} Extension;
-/
public
structure Extension (Bytes: Type) [BytesLike Bytes] where
  extensionType: ExtensionType
  extensionData: MlsBytes Bytes

@[expose]
public
def Extension.f: ExtensionType × MlsBytes Bytes → Extension Bytes :=
  fun (extensionType, extensionData) => { extensionType, extensionData }
@[expose]
public
def Extension.g: Extension Bytes → ExtensionType × MlsBytes Bytes :=
  fun { extensionType, extensionData } => (extensionType, extensionData)

public
instance: LeftInverse (Extension.g (Bytes := Bytes)) Extension.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (Extension.g (Bytes := Bytes)) Extension.f := ⟨by intro _; rfl⟩

@[expose]
public
def Extension.mf: NonExtensibleMessageFormat Bytes (Extension Bytes) :=
  .isomorphic (.prod ExtensionType.mf MlsBytes.mf) Extension.f Extension.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem Extension.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Extension Bytes):
  (Extension.mf (Bytes := Bytes)).wf pred x = pred x.extensionData.val
:= by
  simp [Extension.mf, Extension.g]

/-! ## Optional -/

@[expose]
public
def MlsOption.internalType (a: Type): Fin 2 → Type
  | 0 => Unit
  | 1 => a

@[expose]
public
def MlsOption.internalType.mf
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  : (present: Fin 2) → NonExtensibleMessageFormat Bytes (internalType a present)
  | 0 => .unit
  | 1 => mf

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.IsNonAmbiguous]
  : ∀ present, (MlsOption.internalType.mf mf present).IsNonAmbiguous
  | 0 | 1 => by
    dsimp only [MlsOption.internalType.mf, MlsOption.internalType]
    infer_instance

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.HasUniqueRepresentation]
  : ∀ present, (MlsOption.internalType.mf mf present).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp only [MlsOption.internalType.mf, MlsOption.internalType]
    infer_instance

/--
struct {
    uint8 present;
    select (present) {
        case 0: struct{};
        case 1: T value;
    }
} optional<T>;
-/
@[expose]
public
def MlsOption.f {a: Type}: (present: Fin 2) × MlsOption.internalType a present → Option a
  | ⟨0, ()⟩ => none
  | ⟨1, x⟩ => some x

@[expose]
public
def MlsOption.g {a: Type}: Option a → (present: Fin 2) × MlsOption.internalType a present
  | none => ⟨0, ()⟩
  | some x => ⟨1, x⟩

public
instance {a: Type}: LeftInverse (MlsOption.g (a := a)) MlsOption.f := ⟨by
  intro ⟨present, x⟩
  match present, x with
  | 0, () => rfl
  | 1, _ => rfl⟩
public
instance {a: Type}: RightInverse (MlsOption.g (a := a)) MlsOption.f := ⟨by intro x; cases x <;> rfl⟩

@[expose]
public
def MlsOption.mf
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  : NonExtensibleMessageFormat Bytes (Option a)
:=
  .isomorphic (.sigma (.fin8 2 (by decide)) (MlsOption.internalType.mf mf)) MlsOption.f MlsOption.g

namespace MlsOption.mf

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.IsNonAmbiguous]
  : (MlsOption.mf mf).IsNonAmbiguous
:= by
  dsimp only [MlsOption.mf]
  infer_instance

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.HasUniqueRepresentation]
  : (MlsOption.mf mf).HasUniqueRepresentation
:= by
  dsimp only [MlsOption.mf]
  infer_instance

public
instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  : (MlsOption.mf mf).ParseConsumes
:= by
  dsimp only [MlsOption.mf]
  infer_instance

@[simp]
public
theorem wf_eq
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Option a)
  : (MlsOption.mf mf).wf pred x = (
      match x with
      | none => True
      | some y => mf.wf pred y
    )
:= by
  cases x <;> simp [MlsOption.mf, MlsOption.g] <;> simp [MlsOption.internalType.mf, MlsOption.internalType]

end MlsOption.mf

/-! ## Static option -/

/-- Special "option" type, when we know statically whether it is a "Some" or "None". -/
@[expose]
public
def StaticOption (b: Bool) (a: Type): Type :=
  match b with
  | true => a
  | false => Unit

@[expose]
public
def StaticOption.mk {b: Bool} {a: Type} (x: a): StaticOption b a :=
  match b with
  | true => x
  | false => ()

/-- The value of a static option known to be present. -/
@[expose]
public
def StaticOption.get {a: Type}: {b: Bool} → StaticOption b a → b = true → a
  | true, x, _ => x

/--
Build a static option in a monad, computing its content only when it is present.
Useful when `b` is not a constructor (e.g. `content.sender.isMember`).
-/
@[expose]
public
def StaticOption.mkM {m: Type → Type} [Pure m] {a: Type}: (b: Bool) → (b = true → m a) → m (StaticOption b a)
  | true, x => x rfl
  | false, _ => pure ()

@[expose]
public
def StaticOption.mf
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a)
  : NonExtensibleMessageFormat Bytes (StaticOption b a)
:=
  match b with
  | true => mf
  | false => .unit

namespace StaticOption.mf

public
instance
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a) [mf.IsNonAmbiguous]
  : (StaticOption.mf b mf).IsNonAmbiguous
:= by
  cases b
  · exact inferInstanceAs (NonExtensibleMessageFormat.unit (Bytes := Bytes)).IsNonAmbiguous
  · exact inferInstanceAs mf.IsNonAmbiguous

public
instance
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a) [mf.HasUniqueRepresentation]
  : (StaticOption.mf b mf).HasUniqueRepresentation
:= by
  cases b
  · exact inferInstanceAs (NonExtensibleMessageFormat.unit (Bytes := Bytes)).HasUniqueRepresentation
  · exact inferInstanceAs mf.HasUniqueRepresentation

@[simp]
public
theorem wf_eq
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: StaticOption b a)
  : (StaticOption.mf b mf).wf pred x = ∀ h: b = true, mf.wf pred (x.get h)
:= by
  cases b
  · exact propext ⟨fun _ h => (nomatch h), fun _ => NonExtensibleMessageFormat.unit.wf_eq pred x⟩
  · simp [StaticOption.mf, StaticOption.get]; rfl

end StaticOption.mf

/-! ## GroupContext -/

/--
struct {
    ProtocolVersion version = mls10;
    CipherSuite cipher_suite;
    opaque group_id<V>;
    uint64 epoch;
    opaque tree_hash<V>;
    opaque confirmed_transcript_hash<V>;
    Extension extensions<V>;
} GroupContext;
-/
public
structure GroupContext (Bytes: Type) [BytesLike Bytes] where
  version: ProtocolVersion
  cipherSuite: CipherSuite
  groupId: MlsBytes Bytes
  epoch: UInt64
  treeHash: MlsBytes Bytes
  confirmedTranscriptHash: MlsBytes Bytes
  extensions: MlsList (Extension.mf (Bytes := Bytes))

@[expose]
public
def GroupContext.f:
  ProtocolVersion × CipherSuite × MlsBytes Bytes × UInt64 × MlsBytes Bytes × MlsBytes Bytes × MlsList (Extension.mf (Bytes := Bytes))
  → GroupContext Bytes
:=
  fun (version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions) =>
    { version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions }

@[expose]
public
def GroupContext.g:
  GroupContext Bytes
  → ProtocolVersion × CipherSuite × MlsBytes Bytes × UInt64 × MlsBytes Bytes × MlsBytes Bytes × MlsList (Extension.mf (Bytes := Bytes))
:=
  fun { version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions } =>
    (version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions)

public
instance: LeftInverse (GroupContext.g (Bytes := Bytes)) GroupContext.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (GroupContext.g (Bytes := Bytes)) GroupContext.f := ⟨by intro _; rfl⟩

@[expose]
public
def GroupContext.mf: NonExtensibleMessageFormat Bytes (GroupContext Bytes) :=
  .isomorphic
    (.prod ProtocolVersion.mf (.prod CipherSuite.mf (.prod MlsBytes.mf (.prod .uint64BE
      (.prod MlsBytes.mf (.prod MlsBytes.mf (MlsList.mf Extension.mf)))))))
    GroupContext.f GroupContext.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem GroupContext.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: GroupContext Bytes):
  (GroupContext.mf (Bytes := Bytes)).wf pred x = (
    pred x.groupId.val ∧ pred x.treeHash.val ∧ pred x.confirmedTranscriptHash.val ∧
    ∀ e ∈ x.extensions.val, Extension.mf.wf pred e
  )
:= by
  simp [GroupContext.mf, GroupContext.g]

/-! ## ProposalType -/

/--
uint16 ProposalType;

Defined here because needed in TreeSync's proposal list in leaf node capabilities.
Actual sum type defined in `MLS.TreeDEM.NetworkTypes`.
-/
public
inductive ProposalType where
  | reserved
  | add
  | update
  | remove
  | psk
  | reinit
  | externalInit
  | groupContextExtensions
  | unknown (n: UInt16) (h: 7 < n.toNat)
deriving DecidableEq

@[expose]
public
def ProposalType.ofUInt16 (n: UInt16): ProposalType :=
  match _: n.toNat with
  | 0 => .reserved
  | 1 => .add
  | 2 => .update
  | 3 => .remove
  | 4 => .psk
  | 5 => .reinit
  | 6 => .externalInit
  | 7 => .groupContextExtensions
  | _+8 => .unknown n (by grind)

@[expose]
public
def ProposalType.toUInt16: ProposalType → UInt16
  | .reserved => 0
  | .add => 1
  | .update => 2
  | .remove => 3
  | .psk => 4
  | .reinit => 5
  | .externalInit => 6
  | .groupContextExtensions => 7
  | .unknown n _ => n

public
instance: LeftInverse ProposalType.toUInt16 ProposalType.ofUInt16 where
  left_inv n := by grind [ProposalType.ofUInt16, ProposalType.toUInt16]

public
instance: RightInverse ProposalType.toUInt16 ProposalType.ofUInt16 where
  right_inv x := by cases x <;> grind [ProposalType.ofUInt16, ProposalType.toUInt16]

@[expose]
public
def ProposalType.mf: NonExtensibleMessageFormat Bytes ProposalType :=
  .isomorphic .uint16BE ProposalType.ofUInt16 ProposalType.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ProposalType.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ProposalType):
  (ProposalType.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [ProposalType.mf]

/-! ## SignaturePublicKey -/

/-- opaque SignaturePublicKey<V>; -/
public
abbrev SignaturePublicKey (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

@[expose]
public
def SignaturePublicKey.mf: NonExtensibleMessageFormat Bytes (SignaturePublicKey Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem SignaturePublicKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: SignaturePublicKey Bytes):
  (SignaturePublicKey.mf (Bytes := Bytes)).wf pred x = pred x.val
:= by
  simp [SignaturePublicKey.mf]

/-! ## CredentialType -/

/-- uint16 CredentialType; -/
public
inductive CredentialType where
  | reserved
  | basic
  | x509
  | unknown (n: UInt16) (h: 2 < n.toNat)
deriving DecidableEq

@[expose]
public
def CredentialType.ofUInt16 (n: UInt16): CredentialType :=
  match _: n.toNat with
  | 0 => .reserved
  | 1 => .basic
  | 2 => .x509
  | _+3 => .unknown n (by grind)

@[expose]
public
def CredentialType.toUInt16: CredentialType → UInt16
  | .reserved => 0
  | .basic => 1
  | .x509 => 2
  | .unknown n _ => n

public
instance: LeftInverse CredentialType.toUInt16 CredentialType.ofUInt16 where
  left_inv n := by grind [CredentialType.ofUInt16, CredentialType.toUInt16]

public
instance: RightInverse CredentialType.toUInt16 CredentialType.ofUInt16 where
  right_inv x := by cases x <;> grind [CredentialType.ofUInt16, CredentialType.toUInt16]

@[expose]
public
def CredentialType.mf: NonExtensibleMessageFormat Bytes CredentialType :=
  .isomorphic .uint16BE CredentialType.ofUInt16 CredentialType.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem CredentialType.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: CredentialType):
  (CredentialType.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [CredentialType.mf]

/-! ## Certificate -/

/--
struct {
    opaque cert_data<V>;
} Certificate;
-/
public
abbrev Certificate (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

@[expose]
public
def Certificate.mf: NonExtensibleMessageFormat Bytes (Certificate Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem Certificate.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Certificate Bytes):
  (Certificate.mf (Bytes := Bytes)).wf pred x = pred x.val
:= by
  simp [Certificate.mf]

/-! ## Credential -/

/--
struct {
    CredentialType credential_type;
    select (Credential.credential_type) {
        case basic:
            opaque identity<V>;

        case x509:
            Certificate chain<V>;
    };
} Credential;
-/
public
inductive Credential (Bytes: Type) [BytesLike Bytes] where
  | basic (identity: MlsBytes Bytes)
  | x509 (chain: MlsList (Certificate.mf (Bytes := Bytes)))

@[expose]
public
def Credential.internalType (Bytes: Type) [BytesLike Bytes]: CredentialType → Type
  | .basic => MlsBytes Bytes
  | .x509 => MlsList (Certificate.mf (Bytes := Bytes))
  | _ => Empty

@[expose]
public
def Credential.internalType.mf: (t: CredentialType) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .basic => MlsBytes.mf
  | .x509 => MlsList.mf Certificate.mf
  | .reserved | .unknown .. => .empty

public
instance: ∀ t, (Credential.internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .basic | .x509 | .reserved | .unknown .. => by
    dsimp only [Credential.internalType.mf, Credential.internalType]
    infer_instance

public
instance: ∀ t, (Credential.internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .basic | .x509 | .reserved | .unknown .. => by
    dsimp only [Credential.internalType.mf, Credential.internalType]
    infer_instance

@[expose]
public
def Credential.f: (t: CredentialType) × Credential.internalType Bytes t → Credential Bytes
  | ⟨.basic, identity⟩ => .basic identity
  | ⟨.x509, chain⟩ => .x509 chain
  | ⟨.reserved, x⟩ | ⟨.unknown .., x⟩ => nomatch x

@[expose]
public
def Credential.g: Credential Bytes → (t: CredentialType) × Credential.internalType Bytes t
  | .basic identity => ⟨.basic, identity⟩
  | .x509 chain => ⟨.x509, chain⟩

public
instance: LeftInverse (Credential.g (Bytes := Bytes)) Credential.f := ⟨by
  intro ⟨t, x⟩; cases t <;> first | rfl | exact nomatch x⟩
public
instance: RightInverse (Credential.g (Bytes := Bytes)) Credential.f := ⟨by
  intro x; cases x <;> rfl⟩

@[expose]
public
def Credential.mf: NonExtensibleMessageFormat Bytes (Credential Bytes) :=
  .isomorphic (.sigma CredentialType.mf Credential.internalType.mf) Credential.f Credential.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem Credential.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Credential Bytes):
  (Credential.mf (Bytes := Bytes)).wf pred x = (
    match x with
    | .basic identity => pred identity.val
    | .x509 chain => ∀ c ∈ chain.val, Certificate.mf.wf pred c
  )
:= by
  cases x <;> simp [Credential.mf, Credential.g] <;> simp [Credential.internalType.mf, Credential.internalType]

end MLS
