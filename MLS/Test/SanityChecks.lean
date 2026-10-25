import MLS.TreeDEM.Code.NetworkTypes
import MLS.TreeSync.Code.Extensions

/-!
Sanity checks: every message format of the NetworkTypes is non-ambiguous,
has unique representation, and (for non-extensible formats) consumes its input.
-/

namespace MLS.NetworkTypes.SanityChecks

open Comparse
open MLS MLS.TreeSync MLS.TreeKEM MLS.Bootstrap MLS.TreeDEM

variable {Bytes: Type} [BytesLike Bytes]
variable (tkt: TreeKEMTypes Bytes) (contentType: ContentType)

/-! ## MLS -/

example: (MlsNat.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (MlsNat.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (MlsNat.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (MlsBytes.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (MlsBytes.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (MlsBytes.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (MlsAsciiString.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (MlsAsciiString.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (MlsAsciiString.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (HpkePublicKey.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (HpkePublicKey.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (HpkePublicKey.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Mac.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Mac.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Mac.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ProtocolVersion.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ProtocolVersion.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ProtocolVersion.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (CipherSuite.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (CipherSuite.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (CipherSuite.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ExtensionType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ExtensionType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ExtensionType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Extension.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Extension.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Extension.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (GroupContext.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (GroupContext.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (GroupContext.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ProposalType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ProposalType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ProposalType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (SignaturePublicKey.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (SignaturePublicKey.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (SignaturePublicKey.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (CredentialType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (CredentialType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (CredentialType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Certificate.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Certificate.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Certificate.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Credential.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Credential.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Credential.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: ((MlsList.mf Extension.mf) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((MlsList.mf Extension.mf) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((MlsList.mf Extension.mf) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: ((MlsOption.mf Extension.mf) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((MlsOption.mf Extension.mf) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((MlsOption.mf Extension.mf) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

/-! ## TreeSync -/

example: (LeafNodeSource.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (LeafNodeSource.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (LeafNodeSource.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Capabilities.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Capabilities.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Capabilities.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Lifetime.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Lifetime.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Lifetime.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: ((LeafNodeData.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((LeafNodeData.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((LeafNodeData.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: ((LeafNode.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((LeafNode.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((LeafNode.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: ((LeafNodeTBS.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((LeafNodeTBS.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((LeafNodeTBS.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: ((ParentNode.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((ParentNode.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((ParentNode.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: (NodeType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (NodeType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (NodeType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: ((Node.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((Node.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((Node.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: ((RatchetTree.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((RatchetTree.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((RatchetTree.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: (ApplicationIdExt.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ApplicationIdExt.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ApplicationIdExt.mf (Bytes := Bytes)).ParseConsumes := inferInstance

/-! ## TreeKEM -/

example: (HpkeCiphertext.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (HpkeCiphertext.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (HpkeCiphertext.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (UpdatePathNode.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (UpdatePathNode.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (UpdatePathNode.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (UpdatePath.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (UpdatePath.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (UpdatePath.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PskType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PskType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PskType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ResumptionPskUsage.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ResumptionPskUsage.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ResumptionPskUsage.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PreSharedKeyId.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PreSharedKeyId.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PreSharedKeyId.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PskLabel.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PskLabel.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PskLabel.mf (Bytes := Bytes)).ParseConsumes := inferInstance

/-! ## Bootstrap -/

example: ((KeyPackageTBS.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((KeyPackageTBS.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((KeyPackageTBS.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: ((KeyPackage.mf tkt) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((KeyPackage.mf tkt) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((KeyPackage.mf tkt) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: (KeyPackageRef.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (KeyPackageRef.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (KeyPackageRef.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (GroupInfoTBS.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (GroupInfoTBS.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (GroupInfoTBS.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (GroupInfo.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (GroupInfo.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (GroupInfo.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PathSecret.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PathSecret.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PathSecret.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (GroupSecrets.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (GroupSecrets.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (GroupSecrets.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (EncryptedGroupSecrets.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (EncryptedGroupSecrets.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (EncryptedGroupSecrets.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Welcome.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Welcome.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Welcome.mf (Bytes := Bytes)).ParseConsumes := inferInstance

/-! ## TreeDEM -/

example: (Add.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Add.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Add.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Update.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Update.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Update.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Remove.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Remove.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Remove.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PreSharedKey.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PreSharedKey.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PreSharedKey.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Reinit.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Reinit.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Reinit.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ExternalInit.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ExternalInit.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ExternalInit.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (GroupContextExtensions.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (GroupContextExtensions.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (GroupContextExtensions.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ProposalRef.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ProposalRef.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ProposalRef.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Proposal.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Proposal.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Proposal.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ProposalOrRef.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ProposalOrRef.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ProposalOrRef.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Commit.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Commit.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Commit.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (SenderType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (SenderType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (SenderType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Sender.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Sender.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Sender.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (WireFormat.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (WireFormat.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (WireFormat.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ContentType.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ContentType.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ContentType.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: ((MlsUntaggedContent.mf contentType) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((MlsUntaggedContent.mf contentType) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((MlsUntaggedContent.mf contentType) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: (MlsTaggedContent.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (MlsTaggedContent.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (MlsTaggedContent.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (FramedContent.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (FramedContent.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (FramedContent.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (FramedContentTBS.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (FramedContentTBS.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (FramedContentTBS.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: ((FramedContentAuthData.mf contentType) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((FramedContentAuthData.mf contentType) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((FramedContentAuthData.mf contentType) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: (AuthenticatedContent.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (AuthenticatedContent.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (AuthenticatedContent.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (AuthenticatedContentTBM.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (AuthenticatedContentTBM.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (AuthenticatedContentTBM.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PublicMessage.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PublicMessage.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PublicMessage.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PrivateMessage.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PrivateMessage.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PrivateMessage.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: ((PrivateMessageContentData.mf contentType) : NonExtensibleMessageFormat Bytes _).IsNonAmbiguous := inferInstance
example: ((PrivateMessageContentData.mf contentType) : NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation := inferInstance
example: ((PrivateMessageContentData.mf contentType) : NonExtensibleMessageFormat Bytes _).ParseConsumes := inferInstance

example: (ZeroByte.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ZeroByte.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ZeroByte.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (PrivateContentAAD.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (PrivateContentAAD.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (PrivateContentAAD.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (SenderData.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (SenderData.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (SenderData.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (SenderDataAAD.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (SenderDataAAD.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (SenderDataAAD.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (ConfirmedTranscriptHashInput.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (ConfirmedTranscriptHashInput.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (ConfirmedTranscriptHashInput.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (InterimTranscriptHashInput.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (InterimTranscriptHashInput.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (InterimTranscriptHashInput.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (Mls10Message.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (Mls10Message.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (Mls10Message.mf (Bytes := Bytes)).ParseConsumes := inferInstance

example: (MlsMessage.mf (Bytes := Bytes)).IsNonAmbiguous := inferInstance
example: (MlsMessage.mf (Bytes := Bytes)).HasUniqueRepresentation := inferInstance
example: (MlsMessage.mf (Bytes := Bytes)).ParseConsumes := inferInstance

/-! ## Extensible formats -/

example: (PrivateMessageContent.mf (Bytes := Bytes) contentType).IsNonAmbiguous := inferInstance
example: (PrivateMessageContent.mf (Bytes := Bytes) contentType).HasUniqueRepresentation := inferInstance

end MLS.NetworkTypes.SanityChecks
