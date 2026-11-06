module

public import MLS.TreeKEM.Code.NetworkTypes

/-!
Port of `MLS.Bootstrap.NetworkTypes`.
-/

namespace MLS.Bootstrap

open Comparse
open MLS
open MLS.TreeSync
open MLS.TreeKEM

variable {Bytes: Type} [BytesLike Bytes]

/-! ## KeyPackage -/

/--
struct {
    ProtocolVersion version;
    CipherSuite cipher_suite;
    HPKEPublicKey init_key;
    LeafNode leaf_node;
    Extension extensions<V>;
} KeyPackageTBS;
-/
public
structure KeyPackageTBS (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  version: ProtocolVersion
  cipherSuite: CipherSuite
  initKey: HpkePublicKey Bytes
  leafNode: LeafNode Bytes tkt
  extensions: MlsList (Extension.mf (Bytes := Bytes))

namespace KeyPackageTBS

variable {tkt: TreeKEMTypes Bytes}

public
abbrev Raw (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  ProtocolVersion × CipherSuite × HpkePublicKey Bytes × LeafNode Bytes tkt × MlsList (Extension.mf (Bytes := Bytes))

public
def f: Raw Bytes tkt → KeyPackageTBS Bytes tkt :=
  fun (version, cipherSuite, initKey, leafNode, extensions) => { version, cipherSuite, initKey, leafNode, extensions }

public
def g: KeyPackageTBS Bytes tkt → Raw Bytes tkt :=
  fun { version, cipherSuite, initKey, leafNode, extensions } => (version, cipherSuite, initKey, leafNode, extensions)

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end KeyPackageTBS

public
def KeyPackageTBS.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (KeyPackageTBS Bytes tkt) :=
  .isomorphic
    (.prod ProtocolVersion.mf (.prod CipherSuite.mf (.prod HpkePublicKey.mf
      (.prod (LeafNode.mf tkt) (MlsList.mf Extension.mf)))))
    KeyPackageTBS.f KeyPackageTBS.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem KeyPackageTBS.mf.wf_eq (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: KeyPackageTBS Bytes tkt):
  (KeyPackageTBS.mf tkt).wf pred x = (
    pred x.initKey.val ∧ (LeafNode.mf tkt).wf pred x.leafNode ∧ ∀ e ∈ x.extensions.val, Extension.mf.wf pred e
  )
:= by
  simp [KeyPackageTBS.mf, KeyPackageTBS.g]

/--
struct {
    ProtocolVersion version;
    CipherSuite cipher_suite;
    HPKEPublicKey init_key;
    LeafNode leaf_node;
    Extension extensions<V>;
    // SignWithLabel(., "KeyPackageTBS", KeyPackageTBS)
    opaque signature<V>;
} KeyPackage;
-/
public
structure KeyPackage (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  tbs: KeyPackageTBS Bytes tkt
  signature: MlsBytes Bytes

namespace KeyPackage

variable {tkt: TreeKEMTypes Bytes}

public
def f: KeyPackageTBS Bytes tkt × MlsBytes Bytes → KeyPackage Bytes tkt :=
  fun (tbs, signature) => { tbs, signature }

public
def g: KeyPackage Bytes tkt → KeyPackageTBS Bytes tkt × MlsBytes Bytes :=
  fun { tbs, signature } => (tbs, signature)

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end KeyPackage

public
def KeyPackage.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (KeyPackage Bytes tkt) :=
  .isomorphic (.prod (KeyPackageTBS.mf tkt) MlsBytes.mf) KeyPackage.f KeyPackage.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem KeyPackage.mf.wf_eq (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: KeyPackage Bytes tkt):
  (KeyPackage.mf tkt).wf pred x = (
    (KeyPackageTBS.mf tkt).wf pred x.tbs ∧ pred x.signature.val
  )
:= by
  simp [KeyPackage.mf, KeyPackage.g]

/-! ## Refs -/

/--
opaque HashReference<V>;

HashReference KeyPackageRef;
-/
public
abbrev KeyPackageRef (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

public
def KeyPackageRef.mf: NonExtensibleMessageFormat Bytes (KeyPackageRef Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem KeyPackageRef.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: KeyPackageRef Bytes):
  (KeyPackageRef.mf (Bytes := Bytes)).wf pred x = pred x.val
:= by
  simp [KeyPackageRef.mf]

/-! ## Welcome -/

/--
struct {
    GroupContext group_context;
    Extension extensions<V>;
    MAC confirmation_tag;
    uint32 signer;
} GroupInfoTBS;
-/
public
structure GroupInfoTBS (Bytes: Type) [BytesLike Bytes] where
  groupContext: GroupContext Bytes
  extensions: MlsList (Extension.mf (Bytes := Bytes))
  confirmationTag: Mac Bytes
  signer: UInt32

namespace GroupInfoTBS

public
abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  GroupContext Bytes × MlsList (Extension.mf (Bytes := Bytes)) × Mac Bytes × UInt32

public
def f: Raw Bytes → GroupInfoTBS Bytes :=
  fun (groupContext, extensions, confirmationTag, signer) => { groupContext, extensions, confirmationTag, signer }

public
def g: GroupInfoTBS Bytes → Raw Bytes :=
  fun { groupContext, extensions, confirmationTag, signer } => (groupContext, extensions, confirmationTag, signer)

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end GroupInfoTBS

public
def GroupInfoTBS.mf: NonExtensibleMessageFormat Bytes (GroupInfoTBS Bytes) :=
  .isomorphic
    (.prod GroupContext.mf (.prod (MlsList.mf Extension.mf) (.prod Mac.mf .uint32BE)))
    GroupInfoTBS.f GroupInfoTBS.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem GroupInfoTBS.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: GroupInfoTBS Bytes):
  (GroupInfoTBS.mf (Bytes := Bytes)).wf pred x = (
    GroupContext.mf.wf pred x.groupContext ∧ (∀ e ∈ x.extensions.val, Extension.mf.wf pred e) ∧ pred x.confirmationTag.val
  )
:= by
  simp [GroupInfoTBS.mf, GroupInfoTBS.g]

/--
struct {
    GroupContext group_context;
    Extension extensions<V>;
    MAC confirmation_tag;
    uint32 signer;
    /* SignWithLabel(., "GroupInfoTBS", GroupInfoTBS) */
    opaque signature<V>;
} GroupInfo;
-/
public
structure GroupInfo (Bytes: Type) [BytesLike Bytes] where
  tbs: GroupInfoTBS Bytes
  signature: MlsBytes Bytes

public
def GroupInfo.f: GroupInfoTBS Bytes × MlsBytes Bytes → GroupInfo Bytes :=
  fun (tbs, signature) => { tbs, signature }

public
def GroupInfo.g: GroupInfo Bytes → GroupInfoTBS Bytes × MlsBytes Bytes :=
  fun { tbs, signature } => (tbs, signature)

public
instance: LeftInverse (GroupInfo.g (Bytes := Bytes)) GroupInfo.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (GroupInfo.g (Bytes := Bytes)) GroupInfo.f := ⟨by intro _; rfl⟩

public
def GroupInfo.mf: NonExtensibleMessageFormat Bytes (GroupInfo Bytes) :=
  .isomorphic (.prod GroupInfoTBS.mf MlsBytes.mf) GroupInfo.f GroupInfo.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem GroupInfo.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: GroupInfo Bytes):
  (GroupInfo.mf (Bytes := Bytes)).wf pred x = (
    GroupInfoTBS.mf.wf pred x.tbs ∧ pred x.signature.val
  )
:= by
  simp [GroupInfo.mf, GroupInfo.g]

/--
struct {
  opaque path_secret<V>;
} PathSecret;
-/
public
structure PathSecret (Bytes: Type) [BytesLike Bytes] where
  pathSecret: MlsBytes Bytes

public
def PathSecret.f: MlsBytes Bytes → PathSecret Bytes :=
  PathSecret.mk

public
def PathSecret.g: PathSecret Bytes → MlsBytes Bytes :=
  PathSecret.pathSecret

public
instance: LeftInverse (PathSecret.g (Bytes := Bytes)) PathSecret.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (PathSecret.g (Bytes := Bytes)) PathSecret.f := ⟨by intro _; rfl⟩

public
def PathSecret.mf: NonExtensibleMessageFormat Bytes (PathSecret Bytes) :=
  .isomorphic MlsBytes.mf PathSecret.f PathSecret.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem PathSecret.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PathSecret Bytes):
  (PathSecret.mf (Bytes := Bytes)).wf pred x = pred x.pathSecret.val
:= by
  simp [PathSecret.mf, PathSecret.g]

/--
struct {
  opaque joiner_secret<V>;
  optional<PathSecret> path_secret;
  PreSharedKeyID psks<V>;
} GroupSecrets;
-/
public
structure GroupSecrets (Bytes: Type) [BytesLike Bytes] where
  joinerSecret: MlsBytes Bytes
  pathSecret: Option (PathSecret Bytes)
  psks: MlsList (PreSharedKeyId.mf (Bytes := Bytes))

namespace GroupSecrets

public
abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  MlsBytes Bytes × Option (PathSecret Bytes) × MlsList (PreSharedKeyId.mf (Bytes := Bytes))

public
def f: Raw Bytes → GroupSecrets Bytes :=
  fun (joinerSecret, pathSecret, psks) => { joinerSecret, pathSecret, psks }

public
def g: GroupSecrets Bytes → Raw Bytes :=
  fun { joinerSecret, pathSecret, psks } => (joinerSecret, pathSecret, psks)

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end GroupSecrets

public
def GroupSecrets.mf: NonExtensibleMessageFormat Bytes (GroupSecrets Bytes) :=
  .isomorphic
    (.prod MlsBytes.mf (.prod (MlsOption.mf PathSecret.mf) (MlsList.mf PreSharedKeyId.mf)))
    GroupSecrets.f GroupSecrets.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem GroupSecrets.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: GroupSecrets Bytes):
  (GroupSecrets.mf (Bytes := Bytes)).wf pred x = (
    pred x.joinerSecret.val ∧ (MlsOption.mf PathSecret.mf).wf pred x.pathSecret ∧
    ∀ psk ∈ x.psks.val, PreSharedKeyId.mf.wf pred psk
  )
:= by
  simp [GroupSecrets.mf, GroupSecrets.g]

/--
struct {
  KeyPackageRef new_member;
  HPKECiphertext encrypted_group_secrets;
} EncryptedGroupSecrets;
-/
public
structure EncryptedGroupSecrets (Bytes: Type) [BytesLike Bytes] where
  newMember: KeyPackageRef Bytes
  encryptedGroupSecrets: HpkeCiphertext Bytes

public
def EncryptedGroupSecrets.f: KeyPackageRef Bytes × HpkeCiphertext Bytes → EncryptedGroupSecrets Bytes :=
  fun (newMember, encryptedGroupSecrets) => { newMember, encryptedGroupSecrets }

public
def EncryptedGroupSecrets.g: EncryptedGroupSecrets Bytes → KeyPackageRef Bytes × HpkeCiphertext Bytes :=
  fun { newMember, encryptedGroupSecrets } => (newMember, encryptedGroupSecrets)

public
instance: LeftInverse (EncryptedGroupSecrets.g (Bytes := Bytes)) EncryptedGroupSecrets.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (EncryptedGroupSecrets.g (Bytes := Bytes)) EncryptedGroupSecrets.f := ⟨by intro _; rfl⟩

public
def EncryptedGroupSecrets.mf: NonExtensibleMessageFormat Bytes (EncryptedGroupSecrets Bytes) :=
  .isomorphic (.prod KeyPackageRef.mf HpkeCiphertext.mf) EncryptedGroupSecrets.f EncryptedGroupSecrets.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem EncryptedGroupSecrets.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: EncryptedGroupSecrets Bytes):
  (EncryptedGroupSecrets.mf (Bytes := Bytes)).wf pred x = (
    pred x.newMember.val ∧ HpkeCiphertext.mf.wf pred x.encryptedGroupSecrets
  )
:= by
  simp [EncryptedGroupSecrets.mf, EncryptedGroupSecrets.g]

/--
struct {
  CipherSuite cipher_suite;
  EncryptedGroupSecrets secrets<V>;
  opaque encrypted_group_info<V>;
} Welcome;
-/
public
structure Welcome (Bytes: Type) [BytesLike Bytes] where
  cipherSuite: CipherSuite
  secrets: MlsList (EncryptedGroupSecrets.mf (Bytes := Bytes))
  encryptedGroupInfo: MlsBytes Bytes

namespace Welcome

public
abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  CipherSuite × MlsList (EncryptedGroupSecrets.mf (Bytes := Bytes)) × MlsBytes Bytes

public
def f: Raw Bytes → Welcome Bytes :=
  fun (cipherSuite, secrets, encryptedGroupInfo) => { cipherSuite, secrets, encryptedGroupInfo }

public
def g: Welcome Bytes → Raw Bytes :=
  fun { cipherSuite, secrets, encryptedGroupInfo } => (cipherSuite, secrets, encryptedGroupInfo)

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end Welcome

public
def Welcome.mf: NonExtensibleMessageFormat Bytes (Welcome Bytes) :=
  .isomorphic
    (.prod CipherSuite.mf (.prod (MlsList.mf EncryptedGroupSecrets.mf) MlsBytes.mf))
    Welcome.f Welcome.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem Welcome.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Welcome Bytes):
  (Welcome.mf (Bytes := Bytes)).wf pred x = (
    (∀ s ∈ x.secrets.val, EncryptedGroupSecrets.mf.wf pred s) ∧ pred x.encryptedGroupInfo.val
  )
:= by
  simp [Welcome.mf, Welcome.g]

end MLS.Bootstrap
