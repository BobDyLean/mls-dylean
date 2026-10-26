module

public import MLS.Symbolic.Code.Parsers
public import MLS.TreeKEM.Code.Types

/-!
Port of `MLS.TreeKEM.Parsers` (the parts needed by the ported proofs).

Port-specific differences:
- Only `ps_treekem_leaf` is ported.
-/

namespace MLS.TreeKEM

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes]

namespace TreeKEMLeaf

@[expose]
public
def f (publicKey: Bytes): TreeKEMLeaf Bytes :=
  { publicKey }

@[expose]
public
def g (x: TreeKEMLeaf Bytes): Bytes :=
  x.publicKey

public
instance: LeftInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (Bytes := Bytes)) f := ⟨by intro _; rfl⟩

end TreeKEMLeaf

/-- Port of `ps_treekem_leaf`. -/
@[expose]
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

end MLS.TreeKEM
