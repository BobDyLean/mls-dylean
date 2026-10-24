import MLS.Common.Code.NetworkTypes

/-!
Port of `MLS.TreeSync.NetworkTypes`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes]

/--
Port of `treekem_types`.
The `hasEq` requirements of the F* version are dropped,
and we additionally require the formats to be non-ambiguous, have unique representation, and consume their input.
-/
structure TreeKEMTypes (Bytes: Type) [BytesLike Bytes] where
  LeafContent: Type
  NodeContent: Type
  mfLeafContent: NonExtensibleMessageFormat Bytes LeafContent
  mfNodeContent: NonExtensibleMessageFormat Bytes NodeContent
  [mfLeafContent_na: mfLeafContent.IsNonAmbiguous]
  [mfLeafContent_ur: mfLeafContent.HasUniqueRepresentation]
  [mfLeafContent_pc: mfLeafContent.ParseConsumes]
  [mfNodeContent_na: mfNodeContent.IsNonAmbiguous]
  [mfNodeContent_ur: mfNodeContent.HasUniqueRepresentation]
  [mfNodeContent_pc: mfNodeContent.ParseConsumes]

attribute [instance] TreeKEMTypes.mfLeafContent_na TreeKEMTypes.mfLeafContent_ur TreeKEMTypes.mfLeafContent_pc
attribute [instance] TreeKEMTypes.mfNodeContent_na TreeKEMTypes.mfNodeContent_ur TreeKEMTypes.mfNodeContent_pc

/-! ## LeafNodeSource -/

/--
enum {
    reserved(0),
    key_package(1),
    update(2),
    commit(3),
    (255)
} LeafNodeSource;
-/
inductive LeafNodeSource where
  | keyPackage
  | update
  | commit
deriving DecidableEq

def LeafNodeSource.ofUInt8 (n: UInt8): Option LeafNodeSource :=
  if n = 1 then some .keyPackage
  else if n = 2 then some .update
  else if n = 3 then some .commit
  else none

def LeafNodeSource.toUInt8: LeafNodeSource → UInt8
  | .keyPackage => 1
  | .update => 2
  | .commit => 3

instance: SubsetLeftInverse LeafNodeSource.toUInt8 LeafNodeSource.ofUInt8 where
  left_inv n := by grind [LeafNodeSource.ofUInt8, LeafNodeSource.toUInt8]

instance: SubsetRightInverse LeafNodeSource.toUInt8 LeafNodeSource.ofUInt8 where
  right_inv x := by cases x <;> rfl

def LeafNodeSource.mf: NonExtensibleMessageFormat Bytes LeafNodeSource :=
  .subsetIsomorphic .uint8 LeafNodeSource.ofUInt8 LeafNodeSource.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Capabilities -/

/--
struct {
    ProtocolVersion versions<V>;
    CipherSuite ciphersuites<V>;
    ExtensionType extensions<V>;
    ProposalType proposals<V>;
    CredentialType credentials<V>;
} Capabilities;
-/
structure Capabilities (Bytes: Type) [BytesLike Bytes] where
  versions: MlsList (ProtocolVersion.mf (Bytes := Bytes))
  ciphersuites: MlsList (CipherSuite.mf (Bytes := Bytes))
  extensions: MlsList (ExtensionType.mf (Bytes := Bytes))
  proposals: MlsList (ProposalType.mf (Bytes := Bytes))
  credentials: MlsList (CredentialType.mf (Bytes := Bytes))

def Capabilities.f:
  MlsList (ProtocolVersion.mf (Bytes := Bytes)) × MlsList (CipherSuite.mf (Bytes := Bytes)) ×
  MlsList (ExtensionType.mf (Bytes := Bytes)) × MlsList (ProposalType.mf (Bytes := Bytes)) ×
  MlsList (CredentialType.mf (Bytes := Bytes))
  → Capabilities Bytes
:=
  fun (versions, ciphersuites, extensions, proposals, credentials) =>
    { versions, ciphersuites, extensions, proposals, credentials }

def Capabilities.g:
  Capabilities Bytes
  → MlsList (ProtocolVersion.mf (Bytes := Bytes)) × MlsList (CipherSuite.mf (Bytes := Bytes)) ×
    MlsList (ExtensionType.mf (Bytes := Bytes)) × MlsList (ProposalType.mf (Bytes := Bytes)) ×
    MlsList (CredentialType.mf (Bytes := Bytes))
:=
  fun { versions, ciphersuites, extensions, proposals, credentials } =>
    (versions, ciphersuites, extensions, proposals, credentials)

instance: LeftInverse (Capabilities.g (Bytes := Bytes)) Capabilities.f := ⟨by intro _; rfl⟩
instance: RightInverse (Capabilities.g (Bytes := Bytes)) Capabilities.f := ⟨by intro _; rfl⟩

def Capabilities.mf: NonExtensibleMessageFormat Bytes (Capabilities Bytes) :=
  .isomorphic
    (.prod (MlsList.mf ProtocolVersion.mf) (.prod (MlsList.mf CipherSuite.mf)
      (.prod (MlsList.mf ExtensionType.mf) (.prod (MlsList.mf ProposalType.mf) (MlsList.mf CredentialType.mf)))))
    Capabilities.f Capabilities.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Lifetime -/

/--
struct {
    uint64 not_before;
    uint64 not_after;
} Lifetime;
-/
structure Lifetime where
  notBefore: UInt64
  notAfter: UInt64

def Lifetime.f: UInt64 × UInt64 → Lifetime :=
  fun (notBefore, notAfter) => { notBefore, notAfter }

def Lifetime.g: Lifetime → UInt64 × UInt64 :=
  fun { notBefore, notAfter } => (notBefore, notAfter)

instance: LeftInverse Lifetime.g Lifetime.f := ⟨by intro _; rfl⟩
instance: RightInverse Lifetime.g Lifetime.f := ⟨by intro _; rfl⟩

def Lifetime.mf: NonExtensibleMessageFormat Bytes Lifetime :=
  .isomorphic (.prod .uint64BE .uint64BE) Lifetime.f Lifetime.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## LeafNode -/

/--
struct {
    HPKEPublicKey encryption_key;
    SignaturePublicKey signature_key;
    Credential credential;
    Capabilities capabilities;

    LeafNodeSource leaf_node_source;
    select (LeafNode.leaf_node_source) {
        case key_package:
            Lifetime lifetime;

        case update:
            struct{};

        case commit:
            opaque parent_hash<V>;
    }

    Extension extensions<V>;
    // SignWithLabel(., "LeafNodeTBS", LeafNodeTBS)
    opaque signature<V>;
} LeafNode;
-/
structure LeafNodeData (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  /-- encryption key -/
  content: tkt.LeafContent
  signatureKey: SignaturePublicKey Bytes
  credential: Credential Bytes
  capabilities: Capabilities Bytes
  source: LeafNodeSource
  lifetime: StaticOption (source == .keyPackage) Lifetime
  parentHash: StaticOption (source == .commit) (MlsBytes Bytes)
  extensions: MlsList (Extension.mf (Bytes := Bytes))

namespace LeafNodeData

variable {tkt: TreeKEMTypes Bytes}

abbrev Raw (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  tkt.LeafContent × SignaturePublicKey Bytes × Credential Bytes × Capabilities Bytes ×
  ((source: LeafNodeSource) ×
    (StaticOption (source == .keyPackage) Lifetime × StaticOption (source == .commit) (MlsBytes Bytes) ×
     MlsList (Extension.mf (Bytes := Bytes))))

def f: Raw Bytes tkt → LeafNodeData Bytes tkt :=
  fun (content, signatureKey, credential, capabilities, ⟨source, lifetime, parentHash, extensions⟩) =>
    { content, signatureKey, credential, capabilities, source, lifetime, parentHash, extensions }

def g: LeafNodeData Bytes tkt → Raw Bytes tkt :=
  fun { content, signatureKey, credential, capabilities, source, lifetime, parentHash, extensions } =>
    (content, signatureKey, credential, capabilities, ⟨source, lifetime, parentHash, extensions⟩)

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end LeafNodeData

def LeafNodeData.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (LeafNodeData Bytes tkt) :=
  .isomorphic
    (.prod tkt.mfLeafContent (.prod SignaturePublicKey.mf (.prod Credential.mf (.prod Capabilities.mf
      (.sigma LeafNodeSource.mf (fun source =>
        .prod (StaticOption.mf (source == .keyPackage) Lifetime.mf)
          (.prod (StaticOption.mf (source == .commit) MlsBytes.mf) (MlsList.mf Extension.mf))))))))
    LeafNodeData.f LeafNodeData.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

structure LeafNode (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  data: LeafNodeData Bytes tkt
  signature: MlsBytes Bytes

namespace LeafNode

variable {tkt: TreeKEMTypes Bytes}

def f: LeafNodeData Bytes tkt × MlsBytes Bytes → LeafNode Bytes tkt :=
  fun (data, signature) => { data, signature }

def g: LeafNode Bytes tkt → LeafNodeData Bytes tkt × MlsBytes Bytes :=
  fun { data, signature } => (data, signature)

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end LeafNode

def LeafNode.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (LeafNode Bytes tkt) :=
  .isomorphic (.prod (LeafNodeData.mf tkt) MlsBytes.mf) LeafNode.f LeafNode.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## LeafNodeTBS -/

/--
struct {
    HPKEPublicKey encryption_key;
    SignaturePublicKey signature_key;
    Credential credential;
    Capabilities capabilities;

    LeafNodeSource leaf_node_source;
    select (LeafNodeTBS.leaf_node_source) {
        case key_package:
            Lifetime lifetime;

        case update:
            struct{};

        case commit:
            opaque parent_hash<V>;
    }

    Extension extensions<V>;

    select (LeafNodeTBS.leaf_node_source) {
        case key_package:
            struct{};

        case update:
            opaque group_id<V>;

        case commit:
            opaque group_id<V>;
    }
} LeafNodeTBS;
-/
structure LeafNodeTBS (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  data: LeafNodeData Bytes tkt
  groupId: StaticOption (data.source == .update || data.source == .commit) (MlsBytes Bytes)
  leafIndex: StaticOption (data.source == .update || data.source == .commit) UInt32

namespace LeafNodeTBS

variable {tkt: TreeKEMTypes Bytes}

abbrev Raw (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  (data: LeafNodeData Bytes tkt) ×
    (StaticOption (data.source == .update || data.source == .commit) (MlsBytes Bytes) ×
     StaticOption (data.source == .update || data.source == .commit) UInt32)

def f: Raw Bytes tkt → LeafNodeTBS Bytes tkt :=
  fun ⟨data, groupId, leafIndex⟩ => { data, groupId, leafIndex }

def g: LeafNodeTBS Bytes tkt → Raw Bytes tkt :=
  fun { data, groupId, leafIndex } => ⟨data, groupId, leafIndex⟩

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end LeafNodeTBS

def LeafNodeTBS.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (LeafNodeTBS Bytes tkt) :=
  .isomorphic
    (.sigma (LeafNodeData.mf tkt) (fun data =>
      .prod (StaticOption.mf (data.source == .update || data.source == .commit) MlsBytes.mf)
        (StaticOption.mf (data.source == .update || data.source == .commit) .uint32BE)))
    LeafNodeTBS.f LeafNodeTBS.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## ParentNode -/

/--
struct {
    HPKEPublicKey encryption_key;
    opaque parent_hash<V>;
    uint32 unmerged_leaves<V>;
} ParentNode;
-/
structure ParentNode (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  /-- encryption key -/
  content: tkt.NodeContent
  parentHash: MlsBytes Bytes
  unmergedLeaves: MlsList (NonExtensibleMessageFormat.uint32BE (Bytes := Bytes))

namespace ParentNode

variable {tkt: TreeKEMTypes Bytes}

def f: tkt.NodeContent × MlsBytes Bytes × MlsList (NonExtensibleMessageFormat.uint32BE (Bytes := Bytes)) → ParentNode Bytes tkt :=
  fun (content, parentHash, unmergedLeaves) => { content, parentHash, unmergedLeaves }

def g: ParentNode Bytes tkt → tkt.NodeContent × MlsBytes Bytes × MlsList (NonExtensibleMessageFormat.uint32BE (Bytes := Bytes)) :=
  fun { content, parentHash, unmergedLeaves } => (content, parentHash, unmergedLeaves)

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end ParentNode

def ParentNode.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (ParentNode Bytes tkt) :=
  .isomorphic (.prod tkt.mfNodeContent (.prod MlsBytes.mf (MlsList.mf .uint32BE))) ParentNode.f ParentNode.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## NodeType -/

/--
enum {
    reserved(0),
    leaf(1),
    parent(2),
    (255)
} NodeType;
-/
inductive NodeType where
  | leaf
  | parent
deriving DecidableEq

def NodeType.ofUInt8 (n: UInt8): Option NodeType :=
  if n = 1 then some .leaf
  else if n = 2 then some .parent
  else none

def NodeType.toUInt8: NodeType → UInt8
  | .leaf => 1
  | .parent => 2

instance: SubsetLeftInverse NodeType.toUInt8 NodeType.ofUInt8 where
  left_inv n := by grind [NodeType.ofUInt8, NodeType.toUInt8]

instance: SubsetRightInverse NodeType.toUInt8 NodeType.ofUInt8 where
  right_inv x := by cases x <;> rfl

def NodeType.mf: NonExtensibleMessageFormat Bytes NodeType :=
  .subsetIsomorphic .uint8 NodeType.ofUInt8 NodeType.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Node -/

/--
struct {
    NodeType node_type;
    select (Node.node_type) {
        case leaf:   LeafNode leaf_node;
        case parent: ParentNode parent_node;
    };
} Node;
-/
inductive Node (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  | leaf: LeafNode Bytes tkt → Node Bytes tkt
  | parent: ParentNode Bytes tkt → Node Bytes tkt

namespace Node

variable {tkt: TreeKEMTypes Bytes}

def internalType (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes): NodeType → Type
  | .leaf => LeafNode Bytes tkt
  | .parent => ParentNode Bytes tkt

def internalType.mf (tkt: TreeKEMTypes Bytes): (t: NodeType) → NonExtensibleMessageFormat Bytes (internalType Bytes tkt t)
  | .leaf => LeafNode.mf tkt
  | .parent => ParentNode.mf tkt

instance: ∀ t, (internalType.mf tkt t).IsNonAmbiguous
  | .leaf | .parent => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf tkt t).HasUniqueRepresentation
  | .leaf | .parent => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: NodeType) × internalType Bytes tkt t → Node Bytes tkt
  | ⟨.leaf, x⟩ => .leaf x
  | ⟨.parent, x⟩ => .parent x

def g: Node Bytes tkt → (t: NodeType) × internalType Bytes tkt t
  | .leaf x => ⟨.leaf, x⟩
  | .parent x => ⟨.parent, x⟩

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro ⟨t, _⟩; cases t <;> rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro x; cases x <;> rfl⟩

end Node

def Node.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (Node Bytes tkt) :=
  .isomorphic (.sigma NodeType.mf (Node.internalType.mf tkt)) Node.f Node.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## RatchetTree -/

/-- optional<Node> ratchet_tree<V>; -/
abbrev RatchetTree (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  MlsList (MlsOption.mf (Node.mf tkt))

def RatchetTree.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (RatchetTree Bytes tkt) :=
  MlsList.mf (MlsOption.mf (Node.mf tkt))
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

end MLS.TreeSync
