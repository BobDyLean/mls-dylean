import Mls.TreeSync.NetworkTypes

/-!
Port of `MLS.TreeKEM.NetworkTypes`.
-/

namespace Mls.TreeKEM

open Comparse
open Mls
open Mls.TreeSync

variable {Bytes: Type} [BytesLike Bytes]

def tkt: TreeKEMTypes Bytes where
  LeafContent := HpkePublicKey Bytes
  NodeContent := HpkePublicKey Bytes
  mfLeafContent := HpkePublicKey.mf
  mfNodeContent := HpkePublicKey.mf

/-! ## HPKECiphertext -/

/--
struct {
    opaque kem_output<V>;
    opaque ciphertext<V>;
} HPKECiphertext;
-/
structure HpkeCiphertext (Bytes: Type) [BytesLike Bytes] where
  kemOutput: MlsBytes Bytes
  ciphertext: MlsBytes Bytes

def HpkeCiphertext.f: MlsBytes Bytes × MlsBytes Bytes → HpkeCiphertext Bytes :=
  fun (kemOutput, ciphertext) => { kemOutput, ciphertext }

def HpkeCiphertext.g: HpkeCiphertext Bytes → MlsBytes Bytes × MlsBytes Bytes :=
  fun { kemOutput, ciphertext } => (kemOutput, ciphertext)

instance: LeftInverse (HpkeCiphertext.g (Bytes := Bytes)) HpkeCiphertext.f := ⟨by intro _; rfl⟩
instance: RightInverse (HpkeCiphertext.g (Bytes := Bytes)) HpkeCiphertext.f := ⟨by intro _; rfl⟩

def HpkeCiphertext.mf: NonExtensibleMessageFormat Bytes (HpkeCiphertext Bytes) :=
  .isomorphic (.prod MlsBytes.mf MlsBytes.mf) HpkeCiphertext.f HpkeCiphertext.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## UpdatePathNode -/

/--
struct {
    HPKEPublicKey encryption_key;
    HPKECiphertext encrypted_path_secret<V>;
} UpdatePathNode;
-/
structure UpdatePathNode (Bytes: Type) [BytesLike Bytes] where
  encryptionKey: HpkePublicKey Bytes
  encryptedPathSecret: MlsList (HpkeCiphertext.mf (Bytes := Bytes))

def UpdatePathNode.f: HpkePublicKey Bytes × MlsList (HpkeCiphertext.mf (Bytes := Bytes)) → UpdatePathNode Bytes :=
  fun (encryptionKey, encryptedPathSecret) => { encryptionKey, encryptedPathSecret }

def UpdatePathNode.g: UpdatePathNode Bytes → HpkePublicKey Bytes × MlsList (HpkeCiphertext.mf (Bytes := Bytes)) :=
  fun { encryptionKey, encryptedPathSecret } => (encryptionKey, encryptedPathSecret)

instance: LeftInverse (UpdatePathNode.g (Bytes := Bytes)) UpdatePathNode.f := ⟨by intro _; rfl⟩
instance: RightInverse (UpdatePathNode.g (Bytes := Bytes)) UpdatePathNode.f := ⟨by intro _; rfl⟩

def UpdatePathNode.mf: NonExtensibleMessageFormat Bytes (UpdatePathNode Bytes) :=
  .isomorphic (.prod HpkePublicKey.mf (MlsList.mf HpkeCiphertext.mf)) UpdatePathNode.f UpdatePathNode.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## UpdatePath -/

/--
struct {
    LeafNode leaf_node;
    UpdatePathNode nodes<V>;
} UpdatePath;
-/
structure UpdatePath (Bytes: Type) [BytesLike Bytes] where
  leafNode: LeafNode Bytes tkt
  nodes: MlsList (UpdatePathNode.mf (Bytes := Bytes))

def UpdatePath.f: LeafNode Bytes tkt × MlsList (UpdatePathNode.mf (Bytes := Bytes)) → UpdatePath Bytes :=
  fun (leafNode, nodes) => { leafNode, nodes }

def UpdatePath.g: UpdatePath Bytes → LeafNode Bytes tkt × MlsList (UpdatePathNode.mf (Bytes := Bytes)) :=
  fun { leafNode, nodes } => (leafNode, nodes)

instance: LeftInverse (UpdatePath.g (Bytes := Bytes)) UpdatePath.f := ⟨by intro _; rfl⟩
instance: RightInverse (UpdatePath.g (Bytes := Bytes)) UpdatePath.f := ⟨by intro _; rfl⟩

def UpdatePath.mf: NonExtensibleMessageFormat Bytes (UpdatePath Bytes) :=
  .isomorphic (.prod (LeafNode.mf tkt) (MlsList.mf UpdatePathNode.mf)) UpdatePath.f UpdatePath.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## PSKs -/

/--
enum {
  reserved(0),
  external(1),
  resumption(2),
  (255)
} PSKType;
-/
inductive PskType where
  | external
  | resumption
deriving DecidableEq

def PskType.ofUInt8 (n: UInt8): Option PskType :=
  if n = 1 then some .external
  else if n = 2 then some .resumption
  else none

def PskType.toUInt8: PskType → UInt8
  | .external => 1
  | .resumption => 2

instance: SubsetLeftInverse PskType.toUInt8 PskType.ofUInt8 where
  left_inv n := by
    unfold PskType.ofUInt8
    by_cases n = 1 <;> by_cases n = 2 <;> simp_all [PskType.toUInt8]

instance: SubsetRightInverse PskType.toUInt8 PskType.ofUInt8 where
  right_inv x := by cases x <;> rfl

def PskType.mf: NonExtensibleMessageFormat Bytes PskType :=
  .subsetIsomorphic .uint8 PskType.ofUInt8 PskType.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
enum {
  reserved(0),
  application(1),
  reinit(2),
  branch(3),
  (255)
} ResumptionPSKUsage;
-/
inductive ResumptionPskUsage where
  | application
  | reinit
  | branch
deriving DecidableEq

def ResumptionPskUsage.ofUInt8 (n: UInt8): Option ResumptionPskUsage :=
  if n = 1 then some .application
  else if n = 2 then some .reinit
  else if n = 3 then some .branch
  else none

def ResumptionPskUsage.toUInt8: ResumptionPskUsage → UInt8
  | .application => 1
  | .reinit => 2
  | .branch => 3

instance: SubsetLeftInverse ResumptionPskUsage.toUInt8 ResumptionPskUsage.ofUInt8 where
  left_inv n := by
    unfold ResumptionPskUsage.ofUInt8
    by_cases n = 1 <;> by_cases n = 2 <;> by_cases n = 3 <;> simp_all [ResumptionPskUsage.toUInt8]

instance: SubsetRightInverse ResumptionPskUsage.toUInt8 ResumptionPskUsage.ofUInt8 where
  right_inv x := by cases x <;> rfl

def ResumptionPskUsage.mf: NonExtensibleMessageFormat Bytes ResumptionPskUsage :=
  .subsetIsomorphic .uint8 ResumptionPskUsage.ofUInt8 ResumptionPskUsage.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
  PSKType psktype;
  select (PreSharedKeyID.psktype) {
    case external:
      opaque psk_id<V>;

    case resumption:
      ResumptionPSKUsage usage;
      opaque psk_group_id<V>;
      uint64 psk_epoch;
  };
  opaque psk_nonce<V>;
} PreSharedKeyID;
-/
inductive PreSharedKeyId (Bytes: Type) [BytesLike Bytes] where
  | external (pskId: MlsBytes Bytes) (pskNonce: MlsBytes Bytes)
  | resumption (usage: ResumptionPskUsage) (pskGroupId: MlsBytes Bytes) (pskEpoch: UInt64) (pskNonce: MlsBytes Bytes)

namespace PreSharedKeyId

def internalType (Bytes: Type) [BytesLike Bytes]: PskType → Type
  | .external => MlsBytes Bytes × MlsBytes Bytes
  | .resumption => ResumptionPskUsage × MlsBytes Bytes × UInt64 × MlsBytes Bytes

def internalType.mf: (t: PskType) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .external => .prod MlsBytes.mf MlsBytes.mf
  | .resumption => .prod ResumptionPskUsage.mf (.prod MlsBytes.mf (.prod .uint64BE MlsBytes.mf))

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .external | .resumption => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .external | .resumption => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: PskType) × internalType Bytes t → PreSharedKeyId Bytes
  | ⟨.external, (pskId, pskNonce)⟩ => .external pskId pskNonce
  | ⟨.resumption, (usage, pskGroupId, pskEpoch, pskNonce)⟩ => .resumption usage pskGroupId pskEpoch pskNonce

def g: PreSharedKeyId Bytes → (t: PskType) × internalType Bytes t
  | .external pskId pskNonce => ⟨.external, (pskId, pskNonce)⟩
  | .resumption usage pskGroupId pskEpoch pskNonce => ⟨.resumption, (usage, pskGroupId, pskEpoch, pskNonce)⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro ⟨t, _⟩; cases t <;> rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro x; cases x <;> rfl⟩

end PreSharedKeyId

def PreSharedKeyId.mf: NonExtensibleMessageFormat Bytes (PreSharedKeyId Bytes) :=
  .isomorphic (.sigma PskType.mf PreSharedKeyId.internalType.mf) PreSharedKeyId.f PreSharedKeyId.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    PreSharedKeyID id;
    uint16 index;
    uint16 count;
} PSKLabel;
-/
structure PskLabel (Bytes: Type) [BytesLike Bytes] where
  id: PreSharedKeyId Bytes
  index: UInt16
  count: UInt16

def PskLabel.f: PreSharedKeyId Bytes × UInt16 × UInt16 → PskLabel Bytes :=
  fun (id, index, count) => { id, index, count }

def PskLabel.g: PskLabel Bytes → PreSharedKeyId Bytes × UInt16 × UInt16 :=
  fun { id, index, count } => (id, index, count)

instance: LeftInverse (PskLabel.g (Bytes := Bytes)) PskLabel.f := ⟨by intro _; rfl⟩
instance: RightInverse (PskLabel.g (Bytes := Bytes)) PskLabel.f := ⟨by intro _; rfl⟩

def PskLabel.mf: NonExtensibleMessageFormat Bytes (PskLabel Bytes) :=
  .isomorphic (.prod PreSharedKeyId.mf (.prod .uint16BE .uint16BE)) PskLabel.f PskLabel.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

end Mls.TreeKEM
