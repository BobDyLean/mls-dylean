import Mls.Bootstrap.NetworkTypes

/-!
Port of `MLS.TreeDEM.NetworkTypes`.
-/

namespace Mls.TreeDEM

open Comparse
open Mls
open Mls.TreeSync
open Mls.TreeKEM
open Mls.Bootstrap

variable {Bytes: Type} [BytesLike Bytes]

/-! ## Proposals -/

/--
struct {
    KeyPackage key_package;
} Add;
-/
structure Add (Bytes: Type) [BytesLike Bytes] where
  keyPackage: KeyPackage Bytes tkt

instance: LeftInverse (Add.keyPackage (Bytes := Bytes)) Add.mk := ⟨by intro _; rfl⟩
instance: RightInverse (Add.keyPackage (Bytes := Bytes)) Add.mk := ⟨by intro _; rfl⟩

def Add.mf: NonExtensibleMessageFormat Bytes (Add Bytes) :=
  .isomorphic (KeyPackage.mf tkt) Add.mk Add.keyPackage
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    LeafNode leaf_node;
} Update;
-/
structure Update (Bytes: Type) [BytesLike Bytes] where
  leafNode: LeafNode Bytes tkt

instance: LeftInverse (Update.leafNode (Bytes := Bytes)) Update.mk := ⟨by intro _; rfl⟩
instance: RightInverse (Update.leafNode (Bytes := Bytes)) Update.mk := ⟨by intro _; rfl⟩

def Update.mf: NonExtensibleMessageFormat Bytes (Update Bytes) :=
  .isomorphic (LeafNode.mf tkt) Update.mk Update.leafNode
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    uint32 removed;
} Remove;
-/
structure Remove where
  removed: UInt32

instance: LeftInverse Remove.removed Remove.mk := ⟨by intro _; rfl⟩
instance: RightInverse Remove.removed Remove.mk := ⟨by intro _; rfl⟩

def Remove.mf: NonExtensibleMessageFormat Bytes Remove :=
  .isomorphic .uint32BE Remove.mk Remove.removed
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    PreSharedKeyID psk;
} PreSharedKey;
-/
structure PreSharedKey (Bytes: Type) [BytesLike Bytes] where
  psk: PreSharedKeyId Bytes

instance: LeftInverse (PreSharedKey.psk (Bytes := Bytes)) PreSharedKey.mk := ⟨by intro _; rfl⟩
instance: RightInverse (PreSharedKey.psk (Bytes := Bytes)) PreSharedKey.mk := ⟨by intro _; rfl⟩

def PreSharedKey.mf: NonExtensibleMessageFormat Bytes (PreSharedKey Bytes) :=
  .isomorphic PreSharedKeyId.mf PreSharedKey.mk PreSharedKey.psk
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    opaque group_id<V>;
    ProtocolVersion version;
    CipherSuite cipher_suite;
    Extension extensions<V>;
} ReInit;
-/
structure Reinit (Bytes: Type) [BytesLike Bytes] where
  groupId: MlsBytes Bytes
  version: ProtocolVersion
  cipherSuite: CipherSuite
  extensions: MlsList (Extension.mf (Bytes := Bytes))

namespace Reinit

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  MlsBytes Bytes × ProtocolVersion × CipherSuite × MlsList (Extension.mf (Bytes := Bytes))

def f: Raw Bytes → Reinit Bytes :=
  fun (groupId, version, cipherSuite, extensions) => { groupId, version, cipherSuite, extensions }

def g: Reinit Bytes → Raw Bytes :=
  fun { groupId, version, cipherSuite, extensions } => (groupId, version, cipherSuite, extensions)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end Reinit

def Reinit.mf: NonExtensibleMessageFormat Bytes (Reinit Bytes) :=
  .isomorphic
    (.prod MlsBytes.mf (.prod ProtocolVersion.mf (.prod CipherSuite.mf (MlsList.mf Extension.mf))))
    Reinit.f Reinit.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
  opaque kem_output<V>;
} ExternalInit;
-/
structure ExternalInit (Bytes: Type) [BytesLike Bytes] where
  kemOutput: MlsBytes Bytes

instance: LeftInverse (ExternalInit.kemOutput (Bytes := Bytes)) ExternalInit.mk := ⟨by intro _; rfl⟩
instance: RightInverse (ExternalInit.kemOutput (Bytes := Bytes)) ExternalInit.mk := ⟨by intro _; rfl⟩

def ExternalInit.mf: NonExtensibleMessageFormat Bytes (ExternalInit Bytes) :=
  .isomorphic MlsBytes.mf ExternalInit.mk ExternalInit.kemOutput
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
  Extension extensions<V>;
} GroupContextExtensions;
-/
structure GroupContextExtensions (Bytes: Type) [BytesLike Bytes] where
  extensions: MlsList (Extension.mf (Bytes := Bytes))

instance: LeftInverse (GroupContextExtensions.extensions (Bytes := Bytes)) GroupContextExtensions.mk := ⟨by intro _; rfl⟩
instance: RightInverse (GroupContextExtensions.extensions (Bytes := Bytes)) GroupContextExtensions.mk := ⟨by intro _; rfl⟩

def GroupContextExtensions.mf: NonExtensibleMessageFormat Bytes (GroupContextExtensions Bytes) :=
  .isomorphic (MlsList.mf Extension.mf) GroupContextExtensions.mk GroupContextExtensions.extensions
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Refs -/

/--
opaque HashReference<V>;

HashReference ProposalRef;
-/
abbrev ProposalRef (Bytes: Type) [BytesLike Bytes] := MlsBytes Bytes

def ProposalRef.mf: NonExtensibleMessageFormat Bytes (ProposalRef Bytes) := MlsBytes.mf
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Message framing -/

/-- uint16 ProposalType; -/
inductive Proposal (Bytes: Type) [BytesLike Bytes] where
  | add: Add Bytes → Proposal Bytes
  | update: Update Bytes → Proposal Bytes
  | remove: Remove → Proposal Bytes
  | psk: PreSharedKey Bytes → Proposal Bytes
  | reinit: Reinit Bytes → Proposal Bytes
  | externalInit: ExternalInit Bytes → Proposal Bytes
  | groupContextExtensions: GroupContextExtensions Bytes → Proposal Bytes

namespace Proposal

def internalType (Bytes: Type) [BytesLike Bytes]: ProposalType → Type
  | .add => Add Bytes
  | .update => Update Bytes
  | .remove => Remove
  | .psk => PreSharedKey Bytes
  | .reinit => Reinit Bytes
  | .externalInit => ExternalInit Bytes
  | .groupContextExtensions => GroupContextExtensions Bytes
  | .reserved | .unknown .. => Empty

def internalType.mf: (t: ProposalType) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .add => Add.mf
  | .update => Update.mf
  | .remove => Remove.mf
  | .psk => PreSharedKey.mf
  | .reinit => Reinit.mf
  | .externalInit => ExternalInit.mf
  | .groupContextExtensions => GroupContextExtensions.mf
  | .reserved | .unknown .. => .empty

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .add | .update | .remove | .psk | .reinit | .externalInit | .groupContextExtensions
  | .reserved | .unknown .. => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .add | .update | .remove | .psk | .reinit | .externalInit | .groupContextExtensions
  | .reserved | .unknown .. => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: ProposalType) × internalType Bytes t → Proposal Bytes
  | ⟨.add, x⟩ => .add x
  | ⟨.update, x⟩ => .update x
  | ⟨.remove, x⟩ => .remove x
  | ⟨.psk, x⟩ => .psk x
  | ⟨.reinit, x⟩ => .reinit x
  | ⟨.externalInit, x⟩ => .externalInit x
  | ⟨.groupContextExtensions, x⟩ => .groupContextExtensions x
  | ⟨.reserved, x⟩ | ⟨.unknown .., x⟩ => nomatch x

def g: Proposal Bytes → (t: ProposalType) × internalType Bytes t
  | .add x => ⟨.add, x⟩
  | .update x => ⟨.update, x⟩
  | .remove x => ⟨.remove, x⟩
  | .psk x => ⟨.psk, x⟩
  | .reinit x => ⟨.reinit, x⟩
  | .externalInit x => ⟨.externalInit, x⟩
  | .groupContextExtensions x => ⟨.groupContextExtensions, x⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by
  intro ⟨t, x⟩; cases t <;> first | rfl | exact nomatch x⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro x; cases x <;> rfl⟩

end Proposal

def Proposal.mf: NonExtensibleMessageFormat Bytes (Proposal Bytes) :=
  .isomorphic (.sigma ProposalType.mf Proposal.internalType.mf) Proposal.f Proposal.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
enum {
  reserved(0),
  proposal(1),
  reference(2),
  (255)
} ProposalOrRefType;

struct {
  ProposalOrRefType type;
  select (ProposalOrRef.type) {
    case proposal:  Proposal proposal;
    case reference: ProposalRef reference;
  };
} ProposalOrRef;
-/
inductive ProposalOrRef (Bytes: Type) [BytesLike Bytes] where
  | proposal: Proposal Bytes → ProposalOrRef Bytes
  | reference: ProposalRef Bytes → ProposalOrRef Bytes

namespace ProposalOrRef

def internalType (Bytes: Type) [BytesLike Bytes]: Fin 3 → Type
  | 1 => Proposal Bytes
  | 2 => ProposalRef Bytes
  | 0 => Empty

def internalType.mf: (t: Fin 3) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | 1 => Proposal.mf
  | 2 => ProposalRef.mf
  | 0 => .empty

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | 0 | 1 | 2 => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | 0 | 1 | 2 => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: Fin 3) × internalType Bytes t → ProposalOrRef Bytes
  | ⟨1, x⟩ => .proposal x
  | ⟨2, x⟩ => .reference x
  | ⟨0, x⟩ => nomatch x

def g: ProposalOrRef Bytes → (t: Fin 3) × internalType Bytes t
  | .proposal x => ⟨1, x⟩
  | .reference x => ⟨2, x⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by
  intro ⟨t, x⟩
  match t, x with
  | 0, x => exact nomatch x
  | 1, _ => rfl
  | 2, _ => rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro x; cases x <;> rfl⟩

end ProposalOrRef

def ProposalOrRef.mf: NonExtensibleMessageFormat Bytes (ProposalOrRef Bytes) :=
  .isomorphic (.sigma (.fin8 3 (by decide)) ProposalOrRef.internalType.mf) ProposalOrRef.f ProposalOrRef.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    ProposalOrRef proposals<V>;
    optional<UpdatePath> path;
} Commit;
-/
structure Commit (Bytes: Type) [BytesLike Bytes] where
  proposals: MlsList (ProposalOrRef.mf (Bytes := Bytes))
  path: Option (UpdatePath Bytes)

def Commit.f: MlsList (ProposalOrRef.mf (Bytes := Bytes)) × Option (UpdatePath Bytes) → Commit Bytes :=
  fun (proposals, path) => { proposals, path }

def Commit.g: Commit Bytes → MlsList (ProposalOrRef.mf (Bytes := Bytes)) × Option (UpdatePath Bytes) :=
  fun { proposals, path } => (proposals, path)

instance: LeftInverse (Commit.g (Bytes := Bytes)) Commit.f := ⟨by intro _; rfl⟩
instance: RightInverse (Commit.g (Bytes := Bytes)) Commit.f := ⟨by intro _; rfl⟩

def Commit.mf: NonExtensibleMessageFormat Bytes (Commit Bytes) :=
  .isomorphic (.prod (MlsList.mf ProposalOrRef.mf) (MlsOption.mf UpdatePath.mf)) Commit.f Commit.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
enum {
    reserved(0),
    member(1),
    external(2),
    new_member_proposal(3),
    new_member_commit(4),
    (255)
} SenderType;
-/
inductive SenderType where
  | member
  | external
  | newMemberProposal
  | newMemberCommit
deriving DecidableEq

def SenderType.ofUInt8 (n: UInt8): Option SenderType :=
  if n = 1 then some .member
  else if n = 2 then some .external
  else if n = 3 then some .newMemberProposal
  else if n = 4 then some .newMemberCommit
  else none

def SenderType.toUInt8: SenderType → UInt8
  | .member => 1
  | .external => 2
  | .newMemberProposal => 3
  | .newMemberCommit => 4

instance: SubsetLeftInverse SenderType.toUInt8 SenderType.ofUInt8 where
  left_inv n := by grind [SenderType.ofUInt8, SenderType.toUInt8]

instance: SubsetRightInverse SenderType.toUInt8 SenderType.ofUInt8 where
  right_inv x := by cases x <;> rfl

def SenderType.mf: NonExtensibleMessageFormat Bytes SenderType :=
  .subsetIsomorphic .uint8 SenderType.ofUInt8 SenderType.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    SenderType sender_type;
    select (Sender.sender_type) {
        case member:
            uint32 leaf_index;
        case external:
            uint32 sender_index;
        case new_member_commit:
        case new_member_proposal:
            struct{};
    };
} Sender;
-/
inductive Sender where
  | member (leafIndex: UInt32)
  | external (senderIndex: UInt32)
  | newMemberProposal
  | newMemberCommit
deriving DecidableEq

namespace Sender

def internalType: SenderType → Type
  | .member => UInt32
  | .external => UInt32
  | .newMemberProposal => Unit
  | .newMemberCommit => Unit

def internalType.mf: (t: SenderType) → NonExtensibleMessageFormat Bytes (internalType t)
  | .member => .uint32BE
  | .external => .uint32BE
  | .newMemberProposal => .unit
  | .newMemberCommit => .unit

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .member | .external | .newMemberProposal | .newMemberCommit => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .member | .external | .newMemberProposal | .newMemberCommit => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: SenderType) × internalType t → Sender
  | ⟨.member, leafIndex⟩ => .member leafIndex
  | ⟨.external, senderIndex⟩ => .external senderIndex
  | ⟨.newMemberProposal, ()⟩ => .newMemberProposal
  | ⟨.newMemberCommit, ()⟩ => .newMemberCommit

def g: Sender → (t: SenderType) × internalType t
  | .member leafIndex => ⟨.member, leafIndex⟩
  | .external senderIndex => ⟨.external, senderIndex⟩
  | .newMemberProposal => ⟨.newMemberProposal, ()⟩
  | .newMemberCommit => ⟨.newMemberCommit, ()⟩

instance: LeftInverse g f := ⟨by intro ⟨t, _⟩; cases t <;> rfl⟩
instance: RightInverse g f := ⟨by intro x; cases x <;> rfl⟩

end Sender

def Sender.mf: NonExtensibleMessageFormat Bytes Sender :=
  .isomorphic (.sigma SenderType.mf Sender.internalType.mf) Sender.f Sender.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- uint16 WireFormat; -/
inductive WireFormat where
  | reserved
  | mlsPublicMessage
  | mlsPrivateMessage
  | mlsWelcome
  | mlsGroupInfo
  | mlsKeyPackage
  | unknown (n: UInt16) (h: 5 < n.toNat)
deriving DecidableEq

def WireFormat.ofUInt16 (n: UInt16): WireFormat :=
  if h: 5 < n.toNat then .unknown n h
  else if n = 0 then .reserved
  else if n = 1 then .mlsPublicMessage
  else if n = 2 then .mlsPrivateMessage
  else if n = 3 then .mlsWelcome
  else if n = 4 then .mlsGroupInfo
  else .mlsKeyPackage

def WireFormat.toUInt16: WireFormat → UInt16
  | .reserved => 0
  | .mlsPublicMessage => 1
  | .mlsPrivateMessage => 2
  | .mlsWelcome => 3
  | .mlsGroupInfo => 4
  | .mlsKeyPackage => 5
  | .unknown n _ => n

instance: LeftInverse WireFormat.toUInt16 WireFormat.ofUInt16 where
  left_inv n := by grind [WireFormat.ofUInt16, WireFormat.toUInt16, ← UInt16.toNat_inj]

instance: RightInverse WireFormat.toUInt16 WireFormat.ofUInt16 where
  right_inv x := by cases x <;> grind [WireFormat.ofUInt16, WireFormat.toUInt16]

def WireFormat.mf: NonExtensibleMessageFormat Bytes WireFormat :=
  .isomorphic .uint16BE WireFormat.ofUInt16 WireFormat.toUInt16
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
enum {
    reserved(0),
    application(1),
    proposal(2),
    commit(3),
    (255)
} ContentType;
-/
inductive ContentType where
  | application
  | proposal
  | commit
deriving DecidableEq

def ContentType.ofUInt8 (n: UInt8): Option ContentType :=
  if n = 1 then some .application
  else if n = 2 then some .proposal
  else if n = 3 then some .commit
  else none

def ContentType.toUInt8: ContentType → UInt8
  | .application => 1
  | .proposal => 2
  | .commit => 3

instance: SubsetLeftInverse ContentType.toUInt8 ContentType.ofUInt8 where
  left_inv n := by grind [ContentType.ofUInt8, ContentType.toUInt8]

instance: SubsetRightInverse ContentType.toUInt8 ContentType.ofUInt8 where
  right_inv x := by cases x <;> rfl

def ContentType.mf: NonExtensibleMessageFormat Bytes ContentType :=
  .subsetIsomorphic .uint8 ContentType.ofUInt8 ContentType.toUInt8
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## FramedContent -/

/--
struct {
    opaque group_id<V>;
    uint64 epoch;
    Sender sender;
    opaque authenticated_data<V>;

    ContentType content_type;
    select (FramedContent.content_type) {
        case application:
          opaque application_data<V>;
        case proposal:
          Proposal proposal;
        case commit:
          Commit commit;
    };
} FramedContent;
-/
def MlsUntaggedContent (Bytes: Type) [BytesLike Bytes]: ContentType → Type
  | .application => MlsBytes Bytes
  | .proposal => Proposal Bytes
  | .commit => Commit Bytes

def MlsUntaggedContent.mf: (contentType: ContentType) → NonExtensibleMessageFormat Bytes (MlsUntaggedContent Bytes contentType)
  | .application => MlsBytes.mf
  | .proposal => Proposal.mf
  | .commit => Commit.mf

instance: ∀ contentType, (MlsUntaggedContent.mf (Bytes := Bytes) contentType).IsNonAmbiguous
  | .application | .proposal | .commit => by
    dsimp only [MlsUntaggedContent.mf, MlsUntaggedContent]
    infer_instance

instance: ∀ contentType, (MlsUntaggedContent.mf (Bytes := Bytes) contentType).HasUniqueRepresentation
  | .application | .proposal | .commit => by
    dsimp only [MlsUntaggedContent.mf, MlsUntaggedContent]
    infer_instance

instance: ∀ contentType, (MlsUntaggedContent.mf (Bytes := Bytes) contentType).ParseConsumes
  | .application | .proposal | .commit => by
    dsimp only [MlsUntaggedContent.mf, MlsUntaggedContent]
    infer_instance

structure MlsTaggedContent (Bytes: Type) [BytesLike Bytes] where
  contentType: ContentType
  content: MlsUntaggedContent Bytes contentType

def MlsTaggedContent.f: (contentType: ContentType) × MlsUntaggedContent Bytes contentType → MlsTaggedContent Bytes :=
  fun ⟨contentType, content⟩ => { contentType, content }

def MlsTaggedContent.g: MlsTaggedContent Bytes → (contentType: ContentType) × MlsUntaggedContent Bytes contentType :=
  fun { contentType, content } => ⟨contentType, content⟩

instance: LeftInverse (MlsTaggedContent.g (Bytes := Bytes)) MlsTaggedContent.f := ⟨by intro _; rfl⟩
instance: RightInverse (MlsTaggedContent.g (Bytes := Bytes)) MlsTaggedContent.f := ⟨by intro _; rfl⟩

def MlsTaggedContent.mf: NonExtensibleMessageFormat Bytes (MlsTaggedContent Bytes) :=
  .isomorphic (.sigma ContentType.mf MlsUntaggedContent.mf) MlsTaggedContent.f MlsTaggedContent.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

structure FramedContent (Bytes: Type) [BytesLike Bytes] where
  groupId: MlsBytes Bytes
  epoch: UInt64
  sender: Sender
  authenticatedData: MlsBytes Bytes
  content: MlsTaggedContent Bytes

namespace FramedContent

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  MlsBytes Bytes × UInt64 × Sender × MlsBytes Bytes × MlsTaggedContent Bytes

def f: Raw Bytes → FramedContent Bytes :=
  fun (groupId, epoch, sender, authenticatedData, content) => { groupId, epoch, sender, authenticatedData, content }

def g: FramedContent Bytes → Raw Bytes :=
  fun { groupId, epoch, sender, authenticatedData, content } => (groupId, epoch, sender, authenticatedData, content)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end FramedContent

def FramedContent.mf: NonExtensibleMessageFormat Bytes (FramedContent Bytes) :=
  .isomorphic
    (.prod MlsBytes.mf (.prod .uint64BE (.prod Sender.mf (.prod MlsBytes.mf MlsTaggedContent.mf))))
    FramedContent.f FramedContent.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## FramedContentTBS -/

/-- Whether the `FramedContentTBS` contains the group context. -/
def Sender.hasGroupContext: Sender → Bool
  | .member .. | .newMemberCommit => true
  | .external .. | .newMemberProposal => false

/--
struct {
    ProtocolVersion version = mls10;
    WireFormat wire_format;
    FramedContent content;
    select (FramedContentTBS.content.sender.sender_type) {
        case member:
        case new_member_commit:
            GroupContext context;
        case external:
        case new_member_proposal:
            struct{};
    };
} FramedContentTBS;
-/
structure FramedContentTBS (Bytes: Type) [BytesLike Bytes] where
  version: ProtocolVersion
  wireFormat: WireFormat
  content: FramedContent Bytes
  groupContext: StaticOption content.sender.hasGroupContext (GroupContext Bytes)

namespace FramedContentTBS

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  ProtocolVersion × WireFormat ×
  ((content: FramedContent Bytes) × StaticOption content.sender.hasGroupContext (GroupContext Bytes))

def f: Raw Bytes → FramedContentTBS Bytes :=
  fun (version, wireFormat, ⟨content, groupContext⟩) => { version, wireFormat, content, groupContext }

def g: FramedContentTBS Bytes → Raw Bytes :=
  fun { version, wireFormat, content, groupContext } => (version, wireFormat, ⟨content, groupContext⟩)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end FramedContentTBS

def FramedContentTBS.mf: NonExtensibleMessageFormat Bytes (FramedContentTBS Bytes) :=
  .isomorphic
    (.prod ProtocolVersion.mf (.prod WireFormat.mf
      (.sigma FramedContent.mf (fun content => StaticOption.mf content.sender.hasGroupContext GroupContext.mf))))
    FramedContentTBS.f FramedContentTBS.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## FramedContentAuthData -/

/--
struct {
    /* SignWithLabel(., "FramedContentTBS", FramedContentTBS) */
    opaque signature<V>;
    select (FramedContent.content_type) {
        case commit:
            /*
              MAC(confirmation_key,
                  GroupContext.confirmed_transcript_hash)
            */
            MAC confirmation_tag;
        case application:
        case proposal:
            struct{};
    };
} FramedContentAuthData;
-/
structure FramedContentAuthData (Bytes: Type) [BytesLike Bytes] (contentType: ContentType) where
  signature: MlsBytes Bytes
  confirmationTag: StaticOption (contentType == .commit) (Mac Bytes)

namespace FramedContentAuthData

variable {contentType: ContentType}

def f: MlsBytes Bytes × StaticOption (contentType == .commit) (Mac Bytes) → FramedContentAuthData Bytes contentType :=
  fun (signature, confirmationTag) => { signature, confirmationTag }

def g: FramedContentAuthData Bytes contentType → MlsBytes Bytes × StaticOption (contentType == .commit) (Mac Bytes) :=
  fun { signature, confirmationTag } => (signature, confirmationTag)

instance: LeftInverse (g (Bytes := Bytes) (contentType := contentType)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes) (contentType := contentType)) f := ⟨by intro _; rfl⟩

end FramedContentAuthData

def FramedContentAuthData.mf (contentType: ContentType): NonExtensibleMessageFormat Bytes (FramedContentAuthData Bytes contentType) :=
  .isomorphic (.prod MlsBytes.mf (StaticOption.mf (contentType == .commit) Mac.mf)) FramedContentAuthData.f FramedContentAuthData.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## AuthenticatedContent -/

/--
struct {
    WireFormat wire_format;
    FramedContent content;
    FramedContentAuthData auth;
} AuthenticatedContent;
-/
structure AuthenticatedContent (Bytes: Type) [BytesLike Bytes] where
  wireFormat: WireFormat
  content: FramedContent Bytes
  auth: FramedContentAuthData Bytes content.content.contentType

namespace AuthenticatedContent

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  WireFormat × ((content: FramedContent Bytes) × FramedContentAuthData Bytes content.content.contentType)

def f: Raw Bytes → AuthenticatedContent Bytes :=
  fun (wireFormat, ⟨content, auth⟩) => { wireFormat, content, auth }

def g: AuthenticatedContent Bytes → Raw Bytes :=
  fun { wireFormat, content, auth } => (wireFormat, ⟨content, auth⟩)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end AuthenticatedContent

def AuthenticatedContent.mf: NonExtensibleMessageFormat Bytes (AuthenticatedContent Bytes) :=
  .isomorphic
    (.prod WireFormat.mf (.sigma FramedContent.mf (fun content => FramedContentAuthData.mf content.content.contentType)))
    AuthenticatedContent.f AuthenticatedContent.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
  FramedContentTBS content_tbs;
  FramedContentAuthData auth;
} AuthenticatedContentTBM;
-/
structure AuthenticatedContentTBM (Bytes: Type) [BytesLike Bytes] where
  contentTbs: FramedContentTBS Bytes
  auth: FramedContentAuthData Bytes contentTbs.content.content.contentType

namespace AuthenticatedContentTBM

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  (contentTbs: FramedContentTBS Bytes) × FramedContentAuthData Bytes contentTbs.content.content.contentType

def f: Raw Bytes → AuthenticatedContentTBM Bytes :=
  fun ⟨contentTbs, auth⟩ => { contentTbs, auth }

def g: AuthenticatedContentTBM Bytes → Raw Bytes :=
  fun { contentTbs, auth } => ⟨contentTbs, auth⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end AuthenticatedContentTBM

def AuthenticatedContentTBM.mf: NonExtensibleMessageFormat Bytes (AuthenticatedContentTBM Bytes) :=
  .isomorphic
    (.sigma FramedContentTBS.mf (fun contentTbs => FramedContentAuthData.mf contentTbs.content.content.contentType))
    AuthenticatedContentTBM.f AuthenticatedContentTBM.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## PublicMessage -/

/-- Whether the `PublicMessage` contains a membership tag. -/
def Sender.isMember: Sender → Bool
  | .member .. => true
  | _ => false

/--
struct {
    FramedContent content;
    FramedContentAuthData auth;
    select (PublicMessage.content.sender.sender_type) {
        case member:
            MAC membership_tag;
        case external:
        case new_member_commit:
        case new_member_proposal:
            struct{};
    };
} PublicMessage;
-/
structure PublicMessage (Bytes: Type) [BytesLike Bytes] where
  content: FramedContent Bytes
  auth: FramedContentAuthData Bytes content.content.contentType
  membershipTag: StaticOption content.sender.isMember (Mac Bytes)

namespace PublicMessage

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  (content: FramedContent Bytes) ×
    (FramedContentAuthData Bytes content.content.contentType × StaticOption content.sender.isMember (Mac Bytes))

def f: Raw Bytes → PublicMessage Bytes :=
  fun ⟨content, auth, membershipTag⟩ => { content, auth, membershipTag }

def g: PublicMessage Bytes → Raw Bytes :=
  fun { content, auth, membershipTag } => ⟨content, auth, membershipTag⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end PublicMessage

def PublicMessage.mf: NonExtensibleMessageFormat Bytes (PublicMessage Bytes) :=
  .isomorphic
    (.sigma FramedContent.mf (fun content =>
      .prod (FramedContentAuthData.mf content.content.contentType) (StaticOption.mf content.sender.isMember Mac.mf)))
    PublicMessage.f PublicMessage.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## PrivateMessage -/

/--
struct {
    opaque group_id<V>;
    uint64 epoch;
    ContentType content_type;
    opaque authenticated_data<V>;
    opaque encrypted_sender_data<V>;
    opaque ciphertext<V>;
} PrivateMessage;
-/
structure PrivateMessage (Bytes: Type) [BytesLike Bytes] where
  groupId: MlsBytes Bytes
  epoch: UInt64
  contentType: ContentType
  authenticatedData: MlsBytes Bytes
  encryptedSenderData: MlsBytes Bytes
  ciphertext: MlsBytes Bytes

namespace PrivateMessage

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  MlsBytes Bytes × UInt64 × ContentType × MlsBytes Bytes × MlsBytes Bytes × MlsBytes Bytes

def f: Raw Bytes → PrivateMessage Bytes :=
  fun (groupId, epoch, contentType, authenticatedData, encryptedSenderData, ciphertext) =>
    { groupId, epoch, contentType, authenticatedData, encryptedSenderData, ciphertext }

def g: PrivateMessage Bytes → Raw Bytes :=
  fun { groupId, epoch, contentType, authenticatedData, encryptedSenderData, ciphertext } =>
    (groupId, epoch, contentType, authenticatedData, encryptedSenderData, ciphertext)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end PrivateMessage

def PrivateMessage.mf: NonExtensibleMessageFormat Bytes (PrivateMessage Bytes) :=
  .isomorphic
    (.prod MlsBytes.mf (.prod .uint64BE (.prod ContentType.mf (.prod MlsBytes.mf (.prod MlsBytes.mf MlsBytes.mf)))))
    PrivateMessage.f PrivateMessage.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## PrivateMessageContent -/

/--
struct {
    select (PrivateMessage.content_type) {
        case application:
          opaque application_data<V>;

        case proposal:
          Proposal proposal;

        case commit:
          Commit commit;
    };

    FramedContentAuthData auth;
    opaque padding[length_of_padding];
} PrivateMessageContent;
-/
structure PrivateMessageContentData (Bytes: Type) [BytesLike Bytes] (contentType: ContentType) where
  content: MlsUntaggedContent Bytes contentType
  auth: FramedContentAuthData Bytes contentType

namespace PrivateMessageContentData

variable {contentType: ContentType}

def f: MlsUntaggedContent Bytes contentType × FramedContentAuthData Bytes contentType → PrivateMessageContentData Bytes contentType :=
  fun (content, auth) => { content, auth }

def g: PrivateMessageContentData Bytes contentType → MlsUntaggedContent Bytes contentType × FramedContentAuthData Bytes contentType :=
  fun { content, auth } => (content, auth)

instance: LeftInverse (g (Bytes := Bytes) (contentType := contentType)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes) (contentType := contentType)) f := ⟨by intro _; rfl⟩

end PrivateMessageContentData

def PrivateMessageContentData.mf (contentType: ContentType): NonExtensibleMessageFormat Bytes (PrivateMessageContentData Bytes contentType) :=
  .isomorphic (.prod (MlsUntaggedContent.mf contentType) (FramedContentAuthData.mf contentType))
    PrivateMessageContentData.f PrivateMessageContentData.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

abbrev ZeroByte := {x: UInt8 // x = 0}

def ZeroByte.mf: NonExtensibleMessageFormat Bytes ZeroByte :=
  .subtype .uint8 (fun x => x = 0)
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

structure PrivateMessageContent (Bytes: Type) [BytesLike Bytes] (contentType: ContentType) where
  data: PrivateMessageContentData Bytes contentType
  padding: List ZeroByte

namespace PrivateMessageContent

variable {contentType: ContentType}

def f: PrivateMessageContentData Bytes contentType × List ZeroByte → PrivateMessageContent Bytes contentType :=
  fun (data, padding) => { data, padding }

def g: PrivateMessageContent Bytes contentType → PrivateMessageContentData Bytes contentType × List ZeroByte :=
  fun { data, padding } => (data, padding)

instance: LeftInverse (g (Bytes := Bytes) (contentType := contentType)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes) (contentType := contentType)) f := ⟨by intro _; rfl⟩

end PrivateMessageContent

/-- Port of `pse_private_message_content_nt`: the padding extends until the end of the buffer. -/
def PrivateMessageContent.mf (contentType: ContentType): ExtensibleMessageFormat Bytes (PrivateMessageContent Bytes contentType) :=
  .isomorphic (.prod (PrivateMessageContentData.mf contentType) (.list ZeroByte.mf))
    PrivateMessageContent.f PrivateMessageContent.g
deriving ExtensibleMessageFormat.IsNonAmbiguous, ExtensibleMessageFormat.HasUniqueRepresentation

/--
struct {
    opaque group_id<V>;
    uint64 epoch;
    ContentType content_type;
    opaque authenticated_data<V>;
} PrivateContentAAD;
-/
structure PrivateContentAAD (Bytes: Type) [BytesLike Bytes] where
  groupId: MlsBytes Bytes
  epoch: UInt64
  contentType: ContentType
  authenticatedData: MlsBytes Bytes

namespace PrivateContentAAD

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  MlsBytes Bytes × UInt64 × ContentType × MlsBytes Bytes

def f: Raw Bytes → PrivateContentAAD Bytes :=
  fun (groupId, epoch, contentType, authenticatedData) => { groupId, epoch, contentType, authenticatedData }

def g: PrivateContentAAD Bytes → Raw Bytes :=
  fun { groupId, epoch, contentType, authenticatedData } => (groupId, epoch, contentType, authenticatedData)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end PrivateContentAAD

def PrivateContentAAD.mf: NonExtensibleMessageFormat Bytes (PrivateContentAAD Bytes) :=
  .isomorphic (.prod MlsBytes.mf (.prod .uint64BE (.prod ContentType.mf MlsBytes.mf)))
    PrivateContentAAD.f PrivateContentAAD.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    uint32 leaf_index;
    uint32 generation;
    opaque reuse_guard[4];
} SenderData;
-/
structure SenderData (Bytes: Type) [BytesLike Bytes] where
  leafIndex: UInt32
  generation: UInt32
  reuseGuard: {b: Bytes // BytesLike.length b = 4}

namespace SenderData

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  UInt32 × UInt32 × {b: Bytes // BytesLike.length b = 4}

def f: Raw Bytes → SenderData Bytes :=
  fun (leafIndex, generation, reuseGuard) => { leafIndex, generation, reuseGuard }

def g: SenderData Bytes → Raw Bytes :=
  fun { leafIndex, generation, reuseGuard } => (leafIndex, generation, reuseGuard)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end SenderData

def SenderData.mf: NonExtensibleMessageFormat Bytes (SenderData Bytes) :=
  .isomorphic (.prod .uint32BE (.prod .uint32BE (.fixedLengthBytes 4))) SenderData.f SenderData.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    opaque group_id<V>;
    uint64 epoch;
    ContentType content_type;
} SenderDataAAD;
-/
structure SenderDataAAD (Bytes: Type) [BytesLike Bytes] where
  groupId: MlsBytes Bytes
  epoch: UInt64
  contentType: ContentType

namespace SenderDataAAD

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  MlsBytes Bytes × UInt64 × ContentType

def f: Raw Bytes → SenderDataAAD Bytes :=
  fun (groupId, epoch, contentType) => { groupId, epoch, contentType }

def g: SenderDataAAD Bytes → Raw Bytes :=
  fun { groupId, epoch, contentType } => (groupId, epoch, contentType)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end SenderDataAAD

def SenderDataAAD.mf: NonExtensibleMessageFormat Bytes (SenderDataAAD Bytes) :=
  .isomorphic (.prod MlsBytes.mf (.prod .uint64BE ContentType.mf)) SenderDataAAD.f SenderDataAAD.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## Transcript hashes -/

/--
struct {
    WireFormat wire_format;
    FramedContent content; /* with content_type == commit */
    opaque signature<V>;
} ConfirmedTranscriptHashInput;
-/
structure ConfirmedTranscriptHashInput (Bytes: Type) [BytesLike Bytes] where
  wireFormat: WireFormat
  content: FramedContent Bytes
  signature: MlsBytes Bytes

namespace ConfirmedTranscriptHashInput

abbrev Raw (Bytes: Type) [BytesLike Bytes] :=
  WireFormat × FramedContent Bytes × MlsBytes Bytes

def f: Raw Bytes → ConfirmedTranscriptHashInput Bytes :=
  fun (wireFormat, content, signature) => { wireFormat, content, signature }

def g: ConfirmedTranscriptHashInput Bytes → Raw Bytes :=
  fun { wireFormat, content, signature } => (wireFormat, content, signature)

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end ConfirmedTranscriptHashInput

def ConfirmedTranscriptHashInput.mf: NonExtensibleMessageFormat Bytes (ConfirmedTranscriptHashInput Bytes) :=
  .isomorphic (.prod WireFormat.mf (.prod FramedContent.mf MlsBytes.mf))
    ConfirmedTranscriptHashInput.f ConfirmedTranscriptHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    MAC confirmation_tag;
} InterimTranscriptHashInput;
-/
structure InterimTranscriptHashInput (Bytes: Type) [BytesLike Bytes] where
  confirmationTag: Mac Bytes

instance: LeftInverse (InterimTranscriptHashInput.confirmationTag (Bytes := Bytes)) InterimTranscriptHashInput.mk := ⟨by intro _; rfl⟩
instance: RightInverse (InterimTranscriptHashInput.confirmationTag (Bytes := Bytes)) InterimTranscriptHashInput.mk := ⟨by intro _; rfl⟩

def InterimTranscriptHashInput.mf: NonExtensibleMessageFormat Bytes (InterimTranscriptHashInput Bytes) :=
  .isomorphic Mac.mf InterimTranscriptHashInput.mk InterimTranscriptHashInput.confirmationTag
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-! ## MLSMessage -/

/--
struct {
    ProtocolVersion version = mls10;
    WireFormat wire_format;
    select (MLSMessage.wire_format) {
        case mls_public_message:
            PublicMessage public_message;
        case mls_private_message:
            PrivateMessage private_message;
        case mls_welcome:
            Welcome welcome;
        case mls_group_info:
            GroupInfo group_info;
        case mls_key_package:
            KeyPackage key_package;
    };
} MLSMessage;
-/
inductive Mls10Message (Bytes: Type) [BytesLike Bytes] where
  | publicMessage: PublicMessage Bytes → Mls10Message Bytes
  | privateMessage: PrivateMessage Bytes → Mls10Message Bytes
  | welcome: Welcome Bytes → Mls10Message Bytes
  | groupInfo: GroupInfo Bytes → Mls10Message Bytes
  | keyPackage: KeyPackage Bytes tkt → Mls10Message Bytes

namespace Mls10Message

def internalType (Bytes: Type) [BytesLike Bytes]: WireFormat → Type
  | .mlsPublicMessage => PublicMessage Bytes
  | .mlsPrivateMessage => PrivateMessage Bytes
  | .mlsWelcome => Welcome Bytes
  | .mlsGroupInfo => GroupInfo Bytes
  | .mlsKeyPackage => KeyPackage Bytes tkt
  | .reserved | .unknown .. => Empty

def internalType.mf: (t: WireFormat) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .mlsPublicMessage => PublicMessage.mf
  | .mlsPrivateMessage => PrivateMessage.mf
  | .mlsWelcome => Welcome.mf
  | .mlsGroupInfo => GroupInfo.mf
  | .mlsKeyPackage => KeyPackage.mf tkt
  | .reserved | .unknown .. => .empty

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .mlsPublicMessage | .mlsPrivateMessage | .mlsWelcome | .mlsGroupInfo | .mlsKeyPackage
  | .reserved | .unknown .. => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .mlsPublicMessage | .mlsPrivateMessage | .mlsWelcome | .mlsGroupInfo | .mlsKeyPackage
  | .reserved | .unknown .. => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: WireFormat) × internalType Bytes t → Mls10Message Bytes
  | ⟨.mlsPublicMessage, x⟩ => .publicMessage x
  | ⟨.mlsPrivateMessage, x⟩ => .privateMessage x
  | ⟨.mlsWelcome, x⟩ => .welcome x
  | ⟨.mlsGroupInfo, x⟩ => .groupInfo x
  | ⟨.mlsKeyPackage, x⟩ => .keyPackage x
  | ⟨.reserved, x⟩ | ⟨.unknown .., x⟩ => nomatch x

def g: Mls10Message Bytes → (t: WireFormat) × internalType Bytes t
  | .publicMessage x => ⟨.mlsPublicMessage, x⟩
  | .privateMessage x => ⟨.mlsPrivateMessage, x⟩
  | .welcome x => ⟨.mlsWelcome, x⟩
  | .groupInfo x => ⟨.mlsGroupInfo, x⟩
  | .keyPackage x => ⟨.mlsKeyPackage, x⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by
  intro ⟨t, x⟩; cases t <;> first | rfl | exact nomatch x⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro x; cases x <;> rfl⟩

end Mls10Message

def Mls10Message.mf: NonExtensibleMessageFormat Bytes (Mls10Message Bytes) :=
  .isomorphic (.sigma WireFormat.mf Mls10Message.internalType.mf) Mls10Message.f Mls10Message.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

inductive MlsMessage (Bytes: Type) [BytesLike Bytes] where
  | mls10: Mls10Message Bytes → MlsMessage Bytes

namespace MlsMessage

def internalType (Bytes: Type) [BytesLike Bytes]: ProtocolVersion → Type
  | .mls10 => Mls10Message Bytes
  | .reserved | .unknown .. => Empty

def internalType.mf: (t: ProtocolVersion) → NonExtensibleMessageFormat Bytes (internalType Bytes t)
  | .mls10 => Mls10Message.mf
  | .reserved | .unknown .. => .empty

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).IsNonAmbiguous
  | .mls10 | .reserved | .unknown .. => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf (Bytes := Bytes) t).HasUniqueRepresentation
  | .mls10 | .reserved | .unknown .. => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: ProtocolVersion) × internalType Bytes t → MlsMessage Bytes
  | ⟨.mls10, x⟩ => .mls10 x
  | ⟨.reserved, x⟩ | ⟨.unknown .., x⟩ => nomatch x

def g: MlsMessage Bytes → (t: ProtocolVersion) × internalType Bytes t
  | .mls10 x => ⟨.mls10, x⟩

instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by
  intro ⟨t, x⟩; cases t <;> first | rfl | exact nomatch x⟩
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro x; cases x <;> rfl⟩

end MlsMessage

def MlsMessage.mf: NonExtensibleMessageFormat Bytes (MlsMessage Bytes) :=
  .isomorphic (.sigma ProtocolVersion.mf MlsMessage.internalType.mf) MlsMessage.f MlsMessage.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

end Mls.TreeDEM
