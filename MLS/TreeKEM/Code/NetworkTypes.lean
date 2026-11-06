module

public import MLS.TreeSync.Code.NetworkTypes

/-!
Port of `MLS.TreeKEM.NetworkTypes`.
-/

namespace MLS.TreeKEM

open Comparse
open MLS
open MLS.TreeSync

variable {Bytes: Type} [BytesLike Bytes]

@[expose]
public
def tkt: TreeKEMTypes Bytes where
  LeafContent := HpkePublicKey Bytes
  NodeContent := HpkePublicKey Bytes
  mfLeafContent := HpkePublicKey.mf
  mfNodeContent := HpkePublicKey.mf

@[simp]
public
theorem tkt.mfLeafContent.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: (tkt (Bytes := Bytes)).LeafContent):
  (tkt (Bytes := Bytes)).mfLeafContent.wf pred x = pred x.val
:=
  HpkePublicKey.mf.wf_eq pred x

@[simp]
public
theorem tkt.mfNodeContent.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: (tkt (Bytes := Bytes)).NodeContent):
  (tkt (Bytes := Bytes)).mfNodeContent.wf pred x = pred x.val
:=
  HpkePublicKey.mf.wf_eq pred x

/-! ## HPKECiphertext -/

/--
struct {
    opaque kem_output<V>;
    opaque ciphertext<V>;
} HPKECiphertext;
-/
public
structure HpkeCiphertext (Bytes: Type) [BytesLike Bytes] where
  kemOutput: MlsBytes Bytes
  ciphertext: MlsBytes Bytes

public
def HpkeCiphertext.f: MlsBytes Bytes × MlsBytes Bytes → HpkeCiphertext Bytes :=
  fun (kemOutput, ciphertext) => { kemOutput, ciphertext }

public
def HpkeCiphertext.g: HpkeCiphertext Bytes → MlsBytes Bytes × MlsBytes Bytes :=
  fun { kemOutput, ciphertext } => (kemOutput, ciphertext)

public
instance: LeftInverse (HpkeCiphertext.g (Bytes := Bytes)) HpkeCiphertext.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (HpkeCiphertext.g (Bytes := Bytes)) HpkeCiphertext.f := ⟨by intro _; rfl⟩

public
def HpkeCiphertext.mf: NonExtensibleMessageFormat Bytes (HpkeCiphertext Bytes) :=
  .isomorphic (.prod MlsBytes.mf MlsBytes.mf) HpkeCiphertext.f HpkeCiphertext.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem HpkeCiphertext.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: HpkeCiphertext Bytes):
  (HpkeCiphertext.mf (Bytes := Bytes)).wf pred x = (
    pred x.kemOutput.val ∧ pred x.ciphertext.val
  )
:= by
  simp [HpkeCiphertext.mf, HpkeCiphertext.g]

/-! ## UpdatePathNode -/

/--
struct {
    HPKEPublicKey encryption_key;
    HPKECiphertext encrypted_path_secret<V>;
} UpdatePathNode;
-/
public
structure UpdatePathNode (Bytes: Type) [BytesLike Bytes] where
  encryptionKey: HpkePublicKey Bytes
  encryptedPathSecret: MlsList (HpkeCiphertext.mf (Bytes := Bytes))

public
def UpdatePathNode.f: HpkePublicKey Bytes × MlsList (HpkeCiphertext.mf (Bytes := Bytes)) → UpdatePathNode Bytes :=
  fun (encryptionKey, encryptedPathSecret) => { encryptionKey, encryptedPathSecret }

public
def UpdatePathNode.g: UpdatePathNode Bytes → HpkePublicKey Bytes × MlsList (HpkeCiphertext.mf (Bytes := Bytes)) :=
  fun { encryptionKey, encryptedPathSecret } => (encryptionKey, encryptedPathSecret)

public
instance: LeftInverse (UpdatePathNode.g (Bytes := Bytes)) UpdatePathNode.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (UpdatePathNode.g (Bytes := Bytes)) UpdatePathNode.f := ⟨by intro _; rfl⟩

public
def UpdatePathNode.mf: NonExtensibleMessageFormat Bytes (UpdatePathNode Bytes) :=
  .isomorphic (.prod HpkePublicKey.mf (MlsList.mf HpkeCiphertext.mf)) UpdatePathNode.f UpdatePathNode.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem UpdatePathNode.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UpdatePathNode Bytes):
  (UpdatePathNode.mf (Bytes := Bytes)).wf pred x = (
    pred x.encryptionKey.val ∧ ∀ c ∈ x.encryptedPathSecret.val, HpkeCiphertext.mf.wf pred c
  )
:= by
  simp [UpdatePathNode.mf, UpdatePathNode.g]

/-! ## UpdatePath -/

/--
struct {
    LeafNode leaf_node;
    UpdatePathNode nodes<V>;
} UpdatePath;
-/
public
structure UpdatePath (Bytes: Type) [BytesLike Bytes] where
  leafNode: LeafNode Bytes tkt
  nodes: MlsList (UpdatePathNode.mf (Bytes := Bytes))

public
def UpdatePath.f: LeafNode Bytes tkt × MlsList (UpdatePathNode.mf (Bytes := Bytes)) → UpdatePath Bytes :=
  fun (leafNode, nodes) => { leafNode, nodes }

public
def UpdatePath.g: UpdatePath Bytes → LeafNode Bytes tkt × MlsList (UpdatePathNode.mf (Bytes := Bytes)) :=
  fun { leafNode, nodes } => (leafNode, nodes)

public
instance: LeftInverse (UpdatePath.g (Bytes := Bytes)) UpdatePath.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (UpdatePath.g (Bytes := Bytes)) UpdatePath.f := ⟨by intro _; rfl⟩

public
def UpdatePath.mf: NonExtensibleMessageFormat Bytes (UpdatePath Bytes) :=
  .isomorphic (.prod (LeafNode.mf tkt) (MlsList.mf UpdatePathNode.mf)) UpdatePath.f UpdatePath.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem UpdatePath.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UpdatePath Bytes):
  (UpdatePath.mf (Bytes := Bytes)).wf pred x = (
    (LeafNode.mf tkt).wf pred x.leafNode ∧ ∀ n ∈ x.nodes.val, UpdatePathNode.mf.wf pred n
  )
:= by
  simp [UpdatePath.mf, UpdatePath.g]

/-! ## PSKs -/

/--
enum {
  reserved(0),
  external(1),
  resumption(2),
  (255)
} PSKType;
-/
public
inductive PskType where
  | external
  | resumption
deriving DecidableEq

public
def PskType.ofUInt8 (n: UInt8): Option PskType :=
  match n with
  | 1 => some .external
  | 2 => some .resumption
  | _ => none

public
def PskType.toUInt8: PskType → UInt8
  | .external => 1
  | .resumption => 2

public
instance: SubsetLeftInverse PskType.toUInt8 PskType.ofUInt8 where
  left_inv n := by grind [PskType.ofUInt8, PskType.toUInt8]

public
instance: SubsetRightInverse PskType.toUInt8 PskType.ofUInt8 where
  right_inv x := by cases x <;> rfl

public
def PskType.mf: NonExtensibleMessageFormat Bytes PskType :=
  .subsetIsomorphic .uint8 PskType.ofUInt8 PskType.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem PskType.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PskType):
  (PskType.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [PskType.mf]

/--
enum {
  reserved(0),
  application(1),
  reinit(2),
  branch(3),
  (255)
} ResumptionPSKUsage;
-/
public
inductive ResumptionPskUsage where
  | application
  | reinit
  | branch
deriving DecidableEq

public
def ResumptionPskUsage.ofUInt8 (n: UInt8): Option ResumptionPskUsage :=
  match n with
  | 1 => some .application
  | 2 => some .reinit
  | 3 => some .branch
  | _ => none

public
def ResumptionPskUsage.toUInt8: ResumptionPskUsage → UInt8
  | .application => 1
  | .reinit => 2
  | .branch => 3

public
instance: SubsetLeftInverse ResumptionPskUsage.toUInt8 ResumptionPskUsage.ofUInt8 where
  left_inv n := by grind [ResumptionPskUsage.ofUInt8, ResumptionPskUsage.toUInt8]

public
instance: SubsetRightInverse ResumptionPskUsage.toUInt8 ResumptionPskUsage.ofUInt8 where
  right_inv x := by cases x <;> rfl

public
def ResumptionPskUsage.mf: NonExtensibleMessageFormat Bytes ResumptionPskUsage :=
  .subsetIsomorphic .uint8 ResumptionPskUsage.ofUInt8 ResumptionPskUsage.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ResumptionPskUsage.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ResumptionPskUsage):
  (ResumptionPskUsage.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [ResumptionPskUsage.mf]

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
public
inductive PreSharedKeyId (Bytes: Type) [BytesLike Bytes] where
  | external (pskId: MlsBytes Bytes) (pskNonce: MlsBytes Bytes)
  | resumption (usage: ResumptionPskUsage) (pskGroupId: MlsBytes Bytes) (pskEpoch: UInt64) (pskNonce: MlsBytes Bytes)

namespace PreSharedKeyId

@[expose]
public
def internalType (Bytes: Type) [BytesLike Bytes]: PskType → Type
  | .external => MlsBytes Bytes × MlsBytes Bytes
  | .resumption => ResumptionPskUsage × MlsBytes Bytes × UInt64 × MlsBytes Bytes

@[expose]
public
def internalType.mf: (t: PskType) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .external => .prod MlsBytes.mf MlsBytes.mf
  | .resumption => .prod ResumptionPskUsage.mf (.prod MlsBytes.mf (.prod .uint64BE MlsBytes.mf))

public
instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .external | .resumption => by
    dsimp only [internalType.mf, internalType]
    infer_instance

public
instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .external | .resumption => by
    dsimp only [internalType.mf, internalType]
    infer_instance

public
def f: (t: PskType) × internalType Bytes t → PreSharedKeyId Bytes
  | ⟨.external, (pskId, pskNonce)⟩ => .external pskId pskNonce
  | ⟨.resumption, (usage, pskGroupId, pskEpoch, pskNonce)⟩ => .resumption usage pskGroupId pskEpoch pskNonce

public
def g: PreSharedKeyId Bytes → (t: PskType) × internalType Bytes t
  | .external pskId pskNonce => ⟨.external, (pskId, pskNonce)⟩
  | .resumption usage pskGroupId pskEpoch pskNonce => ⟨.resumption, (usage, pskGroupId, pskEpoch, pskNonce)⟩

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro ⟨t, _⟩; cases t <;> rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro x; cases x <;> rfl⟩

end PreSharedKeyId

public
def PreSharedKeyId.mf: NonExtensibleMessageFormat Bytes (PreSharedKeyId Bytes) :=
  .isomorphic (.sigma PskType.mf PreSharedKeyId.internalType.mf) PreSharedKeyId.f PreSharedKeyId.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem PreSharedKeyId.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PreSharedKeyId Bytes):
  (PreSharedKeyId.mf (Bytes := Bytes)).wf pred x = (
    match x with
    | .external pskId pskNonce => pred pskId.val ∧ pred pskNonce.val
    | .resumption _ pskGroupId _ pskNonce => pred pskGroupId.val ∧ pred pskNonce.val
  )
:= by
  cases x <;> simp [PreSharedKeyId.mf, PreSharedKeyId.g] <;> simp [PreSharedKeyId.internalType.mf, PreSharedKeyId.internalType]

/--
struct {
    PreSharedKeyID id;
    uint16 index;
    uint16 count;
} PSKLabel;
-/
public
structure PskLabel (Bytes: Type) [BytesLike Bytes] where
  id: PreSharedKeyId Bytes
  index: UInt16
  count: UInt16

public
def PskLabel.f: PreSharedKeyId Bytes × UInt16 × UInt16 → PskLabel Bytes :=
  fun (id, index, count) => { id, index, count }

public
def PskLabel.g: PskLabel Bytes → PreSharedKeyId Bytes × UInt16 × UInt16 :=
  fun { id, index, count } => (id, index, count)

public
instance: LeftInverse (PskLabel.g (Bytes := Bytes)) PskLabel.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (PskLabel.g (Bytes := Bytes)) PskLabel.f := ⟨by intro _; rfl⟩

public
def PskLabel.mf: NonExtensibleMessageFormat Bytes (PskLabel Bytes) :=
  .isomorphic (.prod PreSharedKeyId.mf (.prod .uint16BE .uint16BE)) PskLabel.f PskLabel.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem PskLabel.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PskLabel Bytes):
  (PskLabel.mf (Bytes := Bytes)).wf pred x = PreSharedKeyId.mf.wf pred x.id
:= by
  simp [PskLabel.mf, PskLabel.g]

end MLS.TreeKEM
