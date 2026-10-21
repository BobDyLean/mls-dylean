import Mls.Comparse.Derived

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

namespace Mls

open Comparse

variable {Bytes: Type} [BytesLike Bytes]

/-! ## MLS variable-length integers, bytes and lists -/

def mlsNatPred (n: Nat): Prop := n < 2^30

instance: DecidablePred mlsNatPred := fun n => inferInstanceAs (Decidable (n < 2^30))

abbrev MlsNat := {n: Nat // mlsNatPred n}

def MlsNat.f (n: {n: QuicNat // mlsNatPred n.val}): MlsNat := ⟨n.val.val, n.property⟩
def MlsNat.g (n: MlsNat): {n: QuicNat // mlsNatPred n.val} :=
  ⟨⟨n.val, by have := n.property; simp only [mlsNatPred] at this; omega⟩, n.property⟩

instance: LeftInverse MlsNat.g MlsNat.f := ⟨by intro _; rfl⟩
instance: RightInverse MlsNat.g MlsNat.f := ⟨by intro _; rfl⟩

def MlsNat.mf: NonExtensibleMessageFormat Bytes MlsNat :=
  .isomorphic (.subtype .quicNat (fun n => mlsNatPred n.val)) MlsNat.f MlsNat.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

abbrev MlsBytes (Bytes: Type) [BytesLike Bytes] := {b: Bytes // mlsNatPred (BytesLike.length b)}

def MlsBytes.mf: NonExtensibleMessageFormat Bytes (MlsBytes Bytes) :=
  .lengthPrefix mlsNatPred MlsNat.mf .bytes

namespace MlsBytes.mf

instance: (MlsBytes.mf (Bytes := Bytes)).IsNonAmbiguous := by
  dsimp only [MlsBytes.mf]
  exact inferInstanceAs (NonExtensibleMessageFormat.lengthPrefix mlsNatPred MlsNat.mf .bytes).IsNonAmbiguous

instance: (MlsBytes.mf (Bytes := Bytes)).HasUniqueRepresentation := by
  dsimp only [MlsBytes.mf]
  exact inferInstanceAs (NonExtensibleMessageFormat.lengthPrefix mlsNatPred MlsNat.mf .bytes).HasUniqueRepresentation

instance: (MlsBytes.mf (Bytes := Bytes)).ParseConsumes := by
  dsimp only [MlsBytes.mf]
  exact inferInstanceAs (NonExtensibleMessageFormat.lengthPrefix mlsNatPred MlsNat.mf .bytes).ParseConsumes

end MlsBytes.mf

abbrev MlsList
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
:=
  {l: List a // mlsNatPred (BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l))}

def MlsList.mf
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
  : NonExtensibleMessageFormat Bytes (MlsList mf)
:=
  .lengthPrefix mlsNatPred MlsNat.mf (.list mf)

namespace MlsList.mf

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] [mf.IsNonAmbiguous]
  : (MlsList.mf mf).IsNonAmbiguous
:= by
  dsimp only [MlsList.mf]
  infer_instance

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] [mf.HasUniqueRepresentation]
  : (MlsList.mf mf).HasUniqueRepresentation
:= by
  dsimp only [MlsList.mf]
  infer_instance

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
  : (MlsList.mf mf).ParseConsumes
:= by
  dsimp only [MlsList.mf]
  infer_instance

end MlsList.mf

/-! ## ASCII strings -/

def isAsciiString (s: String): Prop := ∀ c ∈ s.toList, c.toNat < 128

instance: DecidablePred isAsciiString := fun s =>
  inferInstanceAs (Decidable (∀ c ∈ s.toList, c.toNat < 128))

/--
Port of `mls_ascii_string`.
We encode ASCII strings with their UTF-8 encoding, which coincides with the ASCII encoding.
-/
abbrev MlsAsciiString :=
  {s: Subtype isAsciiString // mlsNatPred (BytesLike.length ((ExtensibleMessageFormat.subtype (Bytes := Bytes) .string isAsciiString).serialize s))}

def MlsAsciiString.mf: NonExtensibleMessageFormat Bytes (MlsAsciiString (Bytes := Bytes)) :=
  .lengthPrefix mlsNatPred MlsNat.mf (.subtype .string isAsciiString)

namespace MlsAsciiString.mf

instance: (MlsAsciiString.mf (Bytes := Bytes)).IsNonAmbiguous := by
  dsimp only [MlsAsciiString.mf]
  infer_instance

instance: (MlsAsciiString.mf (Bytes := Bytes)).HasUniqueRepresentation := by
  dsimp only [MlsAsciiString.mf]
  infer_instance

instance: (MlsAsciiString.mf (Bytes := Bytes)).ParseConsumes := by
  dsimp only [MlsAsciiString.mf]
  infer_instance

end MlsAsciiString.mf

/-! ## HPKEPublicKey, MAC -/

/-- opaque HPKEPublicKey<V>; -/
abbrev HpkePublicKey (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

def HpkePublicKey.mf: NonExtensibleMessageFormat Bytes (HpkePublicKey Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- opaque MAC<V>; -/
abbrev Mac (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

def Mac.mf: NonExtensibleMessageFormat Bytes (Mac Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## ProtocolVersion -/

/--
enum {
    reserved(0),
    mls10(1),
    (255)
} ProtocolVersion;
-/
inductive ProtocolVersion where
  | reserved
  | mls10
  | unknown (n: UInt16) (h: 1 < n.toNat)
deriving DecidableEq

def ProtocolVersion.ofUInt16 (n: UInt16): ProtocolVersion :=
  if h: 1 < n.toNat then .unknown n h
  else if n = 0 then .reserved
  else .mls10

def ProtocolVersion.toUInt16: ProtocolVersion → UInt16
  | .reserved => 0
  | .mls10 => 1
  | .unknown n _ => n

instance: LeftInverse ProtocolVersion.toUInt16 ProtocolVersion.ofUInt16 where
  left_inv := by
    intro n
    unfold ProtocolVersion.ofUInt16
    repeat' split
    all_goals simp_all [ProtocolVersion.toUInt16, ← UInt16.toNat_inj]
    omega

instance: RightInverse ProtocolVersion.toUInt16 ProtocolVersion.ofUInt16 where
  right_inv := by
    intro x
    cases x <;> simp_all [ProtocolVersion.ofUInt16, ProtocolVersion.toUInt16]

def ProtocolVersion.mf: NonExtensibleMessageFormat Bytes ProtocolVersion :=
  .isomorphic .uint16BE ProtocolVersion.ofUInt16 ProtocolVersion.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## CipherSuite -/

/-- uint16 CipherSuite; -/
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

def CipherSuite.ofUInt16 (n: UInt16): CipherSuite :=
  if h: 7 < n.toNat then .unknown n h
  else if n = 0 then .reserved
  else if n = 1 then .mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  else if n = 2 then .mls_128_dhkemp256_aes128gcm_sha256_p256
  else if n = 3 then .mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  else if n = 4 then .mls_256_dhkemx448_aes256gcm_sha512_ed448
  else if n = 5 then .mls_256_dhkemp521_aes256gcm_sha512_p521
  else if n = 6 then .mls_256_dhkemx448_chacha20poly1305_sha512_ed448
  else .mls_256_dhkemp384_aes256gcm_sha384_p384

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

instance: LeftInverse CipherSuite.toUInt16 CipherSuite.ofUInt16 where
  left_inv := by
    intro n
    unfold CipherSuite.ofUInt16
    repeat' split
    all_goals simp_all [CipherSuite.toUInt16, ← UInt16.toNat_inj]
    omega

instance: RightInverse CipherSuite.toUInt16 CipherSuite.ofUInt16 where
  right_inv := by
    intro x
    cases x <;> simp_all [CipherSuite.ofUInt16, CipherSuite.toUInt16]

def CipherSuite.mf: NonExtensibleMessageFormat Bytes CipherSuite :=
  .isomorphic .uint16BE CipherSuite.ofUInt16 CipherSuite.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## ExtensionType -/

/-- uint16 ExtensionType; -/
inductive ExtensionType where
  | reserved
  | applicationId
  | ratchetTree
  | requiredCapabilities
  | externalPub
  | externalSenders
  | unknown (n: UInt16) (h: 5 < n.toNat)
deriving DecidableEq

def ExtensionType.ofUInt16 (n: UInt16): ExtensionType :=
  if h: 5 < n.toNat then .unknown n h
  else if n = 0 then .reserved
  else if n = 1 then .applicationId
  else if n = 2 then .ratchetTree
  else if n = 3 then .requiredCapabilities
  else if n = 4 then .externalPub
  else .externalSenders

def ExtensionType.toUInt16: ExtensionType → UInt16
  | .reserved => 0
  | .applicationId => 1
  | .ratchetTree => 2
  | .requiredCapabilities => 3
  | .externalPub => 4
  | .externalSenders => 5
  | .unknown n _ => n

instance: LeftInverse ExtensionType.toUInt16 ExtensionType.ofUInt16 where
  left_inv := by
    intro n
    unfold ExtensionType.ofUInt16
    repeat' split
    all_goals simp_all [ExtensionType.toUInt16, ← UInt16.toNat_inj]
    omega

instance: RightInverse ExtensionType.toUInt16 ExtensionType.ofUInt16 where
  right_inv := by
    intro x
    cases x <;> simp_all [ExtensionType.ofUInt16, ExtensionType.toUInt16]

def ExtensionType.mf: NonExtensibleMessageFormat Bytes ExtensionType :=
  .isomorphic .uint16BE ExtensionType.ofUInt16 ExtensionType.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Extension -/

/--
struct {
    ExtensionType extension_type;
    opaque extension_data<V>;
} Extension;
-/
structure Extension (Bytes: Type) [BytesLike Bytes] where
  extensionType: ExtensionType
  extensionData: MlsBytes Bytes

def Extension.f: ExtensionType × MlsBytes Bytes → Extension Bytes :=
  fun (extensionType, extensionData) => { extensionType, extensionData }
def Extension.g: Extension Bytes → ExtensionType × MlsBytes Bytes :=
  fun { extensionType, extensionData } => (extensionType, extensionData)

instance: LeftInverse (Extension.g (Bytes := Bytes)) Extension.f := ⟨by intro _; rfl⟩
instance: RightInverse (Extension.g (Bytes := Bytes)) Extension.f := ⟨by intro _; rfl⟩

def Extension.mf: NonExtensibleMessageFormat Bytes (Extension Bytes) :=
  .isomorphic (.prod ExtensionType.mf MlsBytes.mf) Extension.f Extension.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Optional -/

def MlsOption.internalType (a: Type): Fin 2 → Type
  | 0 => Unit
  | 1 => a

def MlsOption.internalType.mf
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  : (present: Fin 2) → NonExtensibleMessageFormat Bytes (internalType a present)
  | 0 => .unit
  | 1 => mf

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.IsNonAmbiguous]
  : ∀ present, (MlsOption.internalType.mf mf present).IsNonAmbiguous
  | 0 | 1 => by
    dsimp only [MlsOption.internalType.mf, MlsOption.internalType]
    infer_instance

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
def MlsOption.f {a: Type}: (present: Fin 2) × MlsOption.internalType a present → Option a
  | ⟨0, ()⟩ => none
  | ⟨1, x⟩ => some x

def MlsOption.g {a: Type}: Option a → (present: Fin 2) × MlsOption.internalType a present
  | none => ⟨0, ()⟩
  | some x => ⟨1, x⟩

instance {a: Type}: LeftInverse (MlsOption.g (a := a)) MlsOption.f := ⟨by
  intro ⟨present, x⟩
  match present, x with
  | 0, () => rfl
  | 1, _ => rfl⟩
instance {a: Type}: RightInverse (MlsOption.g (a := a)) MlsOption.f := ⟨by intro x; cases x <;> rfl⟩

def MlsOption.mf
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  : NonExtensibleMessageFormat Bytes (Option a)
:=
  .isomorphic (.sigma (.fin8 2 (by decide)) (MlsOption.internalType.mf mf)) MlsOption.f MlsOption.g

namespace MlsOption.mf

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.IsNonAmbiguous]
  : (MlsOption.mf mf).IsNonAmbiguous
:= by
  dsimp only [MlsOption.mf]
  infer_instance

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.HasUniqueRepresentation]
  : (MlsOption.mf mf).HasUniqueRepresentation
:= by
  dsimp only [MlsOption.mf]
  infer_instance

instance
  {a: Type} (mf: NonExtensibleMessageFormat Bytes a)
  : (MlsOption.mf mf).ParseConsumes
:= by
  dsimp only [MlsOption.mf]
  infer_instance

end MlsOption.mf

/-! ## Static option -/

/-- Special "option" type, when we know statically whether it is a "Some" or "None". -/
def StaticOption (b: Bool) (a: Type): Type :=
  match b with
  | true => a
  | false => Unit

def StaticOption.mk {b: Bool} {a: Type} (x: a): StaticOption b a :=
  match b with
  | true => x
  | false => ()

def StaticOption.mf
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a)
  : NonExtensibleMessageFormat Bytes (StaticOption b a)
:=
  match b with
  | true => mf
  | false => .unit

namespace StaticOption.mf

instance
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a) [mf.IsNonAmbiguous]
  : (StaticOption.mf b mf).IsNonAmbiguous
:= by
  cases b
  · exact inferInstanceAs (NonExtensibleMessageFormat.unit (Bytes := Bytes)).IsNonAmbiguous
  · exact inferInstanceAs mf.IsNonAmbiguous

instance
  {a: Type} (b: Bool) (mf: NonExtensibleMessageFormat Bytes a) [mf.HasUniqueRepresentation]
  : (StaticOption.mf b mf).HasUniqueRepresentation
:= by
  cases b
  · exact inferInstanceAs (NonExtensibleMessageFormat.unit (Bytes := Bytes)).HasUniqueRepresentation
  · exact inferInstanceAs mf.HasUniqueRepresentation

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
structure GroupContext (Bytes: Type) [BytesLike Bytes] where
  version: ProtocolVersion
  cipherSuite: CipherSuite
  groupId: MlsBytes Bytes
  epoch: UInt64
  treeHash: MlsBytes Bytes
  confirmedTranscriptHash: MlsBytes Bytes
  extensions: MlsList (Extension.mf (Bytes := Bytes))

def GroupContext.f:
  ProtocolVersion × CipherSuite × MlsBytes Bytes × UInt64 × MlsBytes Bytes × MlsBytes Bytes × MlsList (Extension.mf (Bytes := Bytes))
  → GroupContext Bytes
:=
  fun (version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions) =>
    { version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions }

def GroupContext.g:
  GroupContext Bytes
  → ProtocolVersion × CipherSuite × MlsBytes Bytes × UInt64 × MlsBytes Bytes × MlsBytes Bytes × MlsList (Extension.mf (Bytes := Bytes))
:=
  fun { version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions } =>
    (version, cipherSuite, groupId, epoch, treeHash, confirmedTranscriptHash, extensions)

instance: LeftInverse (GroupContext.g (Bytes := Bytes)) GroupContext.f := ⟨by intro _; rfl⟩
instance: RightInverse (GroupContext.g (Bytes := Bytes)) GroupContext.f := ⟨by intro _; rfl⟩

def GroupContext.mf: NonExtensibleMessageFormat Bytes (GroupContext Bytes) :=
  .isomorphic
    (.prod ProtocolVersion.mf (.prod CipherSuite.mf (.prod MlsBytes.mf (.prod .uint64BE
      (.prod MlsBytes.mf (.prod MlsBytes.mf (MlsList.mf Extension.mf)))))))
    GroupContext.f GroupContext.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## ProposalType -/

/--
uint16 ProposalType;

Defined here because needed in TreeSync's proposal list in leaf node capabilities.
Actual sum type defined in `Mls.TreeDEM.NetworkTypes`.
-/
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

def ProposalType.ofUInt16 (n: UInt16): ProposalType :=
  if h: 7 < n.toNat then .unknown n h
  else if n = 0 then .reserved
  else if n = 1 then .add
  else if n = 2 then .update
  else if n = 3 then .remove
  else if n = 4 then .psk
  else if n = 5 then .reinit
  else if n = 6 then .externalInit
  else .groupContextExtensions

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

instance: LeftInverse ProposalType.toUInt16 ProposalType.ofUInt16 where
  left_inv := by
    intro n
    unfold ProposalType.ofUInt16
    repeat' split
    all_goals simp_all [ProposalType.toUInt16, ← UInt16.toNat_inj]
    omega

instance: RightInverse ProposalType.toUInt16 ProposalType.ofUInt16 where
  right_inv := by
    intro x
    cases x <;> simp_all [ProposalType.ofUInt16, ProposalType.toUInt16]

def ProposalType.mf: NonExtensibleMessageFormat Bytes ProposalType :=
  .isomorphic .uint16BE ProposalType.ofUInt16 ProposalType.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## SignaturePublicKey -/

/-- opaque SignaturePublicKey<V>; -/
abbrev SignaturePublicKey (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

def SignaturePublicKey.mf: NonExtensibleMessageFormat Bytes (SignaturePublicKey Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## CredentialType -/

/-- uint16 CredentialType; -/
inductive CredentialType where
  | reserved
  | basic
  | x509
  | unknown (n: UInt16) (h: 2 < n.toNat)
deriving DecidableEq

def CredentialType.ofUInt16 (n: UInt16): CredentialType :=
  if h: 2 < n.toNat then .unknown n h
  else if n = 0 then .reserved
  else if n = 1 then .basic
  else .x509

def CredentialType.toUInt16: CredentialType → UInt16
  | .reserved => 0
  | .basic => 1
  | .x509 => 2
  | .unknown n _ => n

instance: LeftInverse CredentialType.toUInt16 CredentialType.ofUInt16 where
  left_inv := by
    intro n
    unfold CredentialType.ofUInt16
    repeat' split
    all_goals simp_all [CredentialType.toUInt16, ← UInt16.toNat_inj]
    omega

instance: RightInverse CredentialType.toUInt16 CredentialType.ofUInt16 where
  right_inv := by
    intro x
    cases x <;> simp_all [CredentialType.ofUInt16, CredentialType.toUInt16]

def CredentialType.mf: NonExtensibleMessageFormat Bytes CredentialType :=
  .isomorphic .uint16BE CredentialType.ofUInt16 CredentialType.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Certificate -/

/--
struct {
    opaque cert_data<V>;
} Certificate;
-/
abbrev Certificate (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

def Certificate.mf: NonExtensibleMessageFormat Bytes (Certificate Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

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
inductive Credential (Bytes: Type) [BytesLike Bytes] where
  | basic (identity: MlsBytes Bytes)
  | x509 (chain: MlsList (Certificate.mf (Bytes := Bytes)))

def Credential.internalType (Bytes: Type) [BytesLike Bytes]: CredentialType → Type
  | .basic => MlsBytes Bytes
  | .x509 => MlsList (Certificate.mf (Bytes := Bytes))
  | _ => Empty

def Credential.internalType.mf: (t: CredentialType) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .basic => MlsBytes.mf
  | .x509 => MlsList.mf Certificate.mf
  | .reserved | .unknown .. => .empty

instance: ∀ t, (Credential.internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .basic | .x509 | .reserved | .unknown .. => by
    dsimp only [Credential.internalType.mf, Credential.internalType]
    infer_instance

instance: ∀ t, (Credential.internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .basic | .x509 | .reserved | .unknown .. => by
    dsimp only [Credential.internalType.mf, Credential.internalType]
    infer_instance

def Credential.f: (t: CredentialType) × Credential.internalType Bytes t → Credential Bytes
  | ⟨.basic, identity⟩ => .basic identity
  | ⟨.x509, chain⟩ => .x509 chain
  | ⟨.reserved, x⟩ | ⟨.unknown .., x⟩ => nomatch x

def Credential.g: Credential Bytes → (t: CredentialType) × Credential.internalType Bytes t
  | .basic identity => ⟨.basic, identity⟩
  | .x509 chain => ⟨.x509, chain⟩

instance: LeftInverse (Credential.g (Bytes := Bytes)) Credential.f := ⟨by
  intro ⟨t, x⟩; cases t <;> first | rfl | exact nomatch x⟩
instance: RightInverse (Credential.g (Bytes := Bytes)) Credential.f := ⟨by
  intro x; cases x <;> rfl⟩

def Credential.mf: NonExtensibleMessageFormat Bytes (Credential Bytes) :=
  .isomorphic (.sigma CredentialType.mf Credential.internalType.mf) Credential.f Credential.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

end Mls
