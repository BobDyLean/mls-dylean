module

public import MLS.Symbolic.Code.Parsers
public import MLS.TreeSync.Code.Types
public import MLS.TreeSync.Code.Invariants.AuthService

/-!
Port of `MLS.TreeSync.Symbolic.Parsers`.

Port-specific differences:
- The formats are `abbrev`s, so that the well-formedness lemmas of `Tree.mf` and `Path.mf` apply to them.
- The `parseable_serializeable` instances are not ported (DyLean has no such class).
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes]

/-- Port of `ps_treesync`. -/
public
abbrev TreeSync.mf (tkt: TreeKEMTypes Bytes) (l: Nat): NonExtensibleMessageFormat Bytes (TreeSync Bytes tkt l) :=
  Tree.mf (MlsOption.mf (LeafNode.mf tkt)) (MlsOption.mf (ParentNode.mf tkt)) l

/-- Port of `ps_as_tokens`. -/
public
abbrev ASTokens.mf {TokenT: Type} (mfToken: NonExtensibleMessageFormat Bytes TokenT) (l: Nat):
  NonExtensibleMessageFormat Bytes (ASTokens TokenT l)
:=
  Tree.mf (MlsOption.mf mfToken) .unit l

/-- Port of `ps_pathsync`. -/
public
abbrev PathSync.mf (tkt: TreeKEMTypes Bytes) (l: Nat): NonExtensibleMessageFormat Bytes (PathSync Bytes tkt l) :=
  Path.mf (LeafNode.mf tkt) (MlsOption.mf tkt.mfNodeContent) l

/-- Port of `ps_external_pathsync`. -/
public
abbrev ExternalPathSync.mf (tkt: TreeKEMTypes Bytes) (l: Nat):
  NonExtensibleMessageFormat Bytes (ExternalPathSync Bytes tkt l)
:=
  Path.mf (LeafNodeData.mf tkt) (MlsOption.mf tkt.mfNodeContent) l

end MLS.TreeSync
