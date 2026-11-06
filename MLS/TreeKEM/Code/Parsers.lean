module

public import MLS.Symbolic.Code.Parsers
public import MLS.TreeKEM.Code.Types

/-!
Port of `MLS.TreeKEM.Parsers`.

Port-specific differences:
- `ps_hpke_private_key` is not ported: HPKE private keys are plain `Bytes` (their length is not in their type),
  serialized with `slowBytes`.
- The formats of trees and paths are `abbrev`s, so that the well-formedness lemmas of `Tree.mf` and `Path.mf` apply to them.
-/

namespace MLS.TreeKEM

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes]

namespace TreeKEMLeaf

public
def f (publicKey: Bytes): TreeKEMLeaf Bytes :=
  { publicKey }

public
def g (x: TreeKEMLeaf Bytes): Bytes :=
  x.publicKey

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end TreeKEMLeaf

/-- Port of `ps_treekem_leaf`. -/
public
def TreeKEMLeaf.mf: NonExtensibleMessageFormat Bytes (TreeKEMLeaf Bytes) :=
  .isomorphic .slowBytes TreeKEMLeaf.f TreeKEMLeaf.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem TreeKEMLeaf.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeKEMLeaf Bytes):
  (TreeKEMLeaf.mf (Bytes := Bytes)).wf pred x = pred x.publicKey
:= by
  simp [TreeKEMLeaf.mf, TreeKEMLeaf.g]

namespace TreeKEMNode

public
def f: Bytes × List Nat → TreeKEMNode Bytes :=
  fun (publicKey, unmergedLeaves) => { publicKey, unmergedLeaves }

public
def g: TreeKEMNode Bytes → Bytes × List Nat :=
  fun { publicKey, unmergedLeaves } => (publicKey, unmergedLeaves)

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end TreeKEMNode

/-- Port of `ps_treekem_node`. -/
public
def TreeKEMNode.mf: NonExtensibleMessageFormat Bytes (TreeKEMNode Bytes) :=
  .isomorphic (.prod .slowBytes (.slowList .slowNat)) TreeKEMNode.f TreeKEMNode.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem TreeKEMNode.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeKEMNode Bytes):
  (TreeKEMNode.mf (Bytes := Bytes)).wf pred x = pred x.publicKey
:= by
  simp [TreeKEMNode.mf, TreeKEMNode.g]

/-- Port of `ps_treekem`. -/
public
abbrev TreeKEM.mf (l: Nat): NonExtensibleMessageFormat Bytes (TreeKEM Bytes l) :=
  Tree.mf (MlsOption.mf TreeKEMLeaf.mf) (MlsOption.mf TreeKEMNode.mf) l

/-- Port of `ps_treekem_priv`. -/
public
abbrev TreeKEMPriv.mf (l: Nat): NonExtensibleMessageFormat Bytes (TreeKEMPriv Bytes l) :=
  Path.mf .slowBytes (MlsOption.mf .slowBytes) l

/-- The format of `pathkem` (MLS*'s `ps_path ps_treekem_leaf (ps_option ps_update_path_node_nt)`). -/
public
abbrev PathKEM.mf (l: Nat): NonExtensibleMessageFormat Bytes (PathKEM Bytes l) :=
  Path.mf TreeKEMLeaf.mf (MlsOption.mf UpdatePathNode.mf) l

end MLS.TreeKEM
