import MLS.Common.Proofs.Crypto.Derived
import DySlop.EquationalTheories.Common

/-!
Decoding of the messages labeled by `get_mls_label` (`SignContent`, `KdfLabel`, `EncryptContext`):
the `decode_tagged_data` of the split functions of SignWithLabel, ExpandWithLabel and EncryptWithLabel.

Port-specific differences: the tags are the labels (`"LeafNodeTBS"`), not the MLS labels (`"MLS 1.0 LeafNodeTBS"`):
the decoding strips the prefix `"MLS 1.0 "` (hence the injectivity of `get_mls_label` is not needed).
-/

namespace MLS

open DY
open Comparse

variable {Bytes: Type} [BytesLike Bytes] {α: Type}

/-- Parse `buf` with `mf`, and strip the prefix `"MLS 1.0 "` from the label of the result. -/
def parseWithMlsLabel (mf: NonExtensibleMessageFormat Bytes α) (label: α → MlsAsciiString (Bytes := Bytes)) (buf: Bytes)
  : Option (String × α)
:=
  match mf.toExtensible.parse buf with
  | some x =>
    match stripPrefix? "MLS 1.0 " (label x).val.val with
    | some l => some (l, x)
    | none => none
  | none => none

theorem parseWithMlsLabel_serializeNE
  (mf: NonExtensibleMessageFormat Bytes α) [mf.IsNonAmbiguous] (label: α → MlsAsciiString (Bytes := Bytes))
  (x: α) (l: String)
  : (label x).val.val = "MLS 1.0 " ++ l →
    parseWithMlsLabel mf label (serializeNE mf x) = some (l, x)
:= by
  intro h
  unfold parseWithMlsLabel
  rw [serializeNE, ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv]
  simp only [h, stripPrefix?_append]

/-- `parse_wf_lemma` for `parseWithMlsLabel`. -/
theorem wf_of_parseWithMlsLabel
  (mf: NonExtensibleMessageFormat Bytes α) [mf.HasUniqueRepresentation] (label: α → MlsAsciiString (Bytes := Bytes))
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (buf: Bytes) (l: String) (x: α)
  : parseWithMlsLabel mf label buf = some (l, x) →
    pred buf →
    mf.wf pred x
:= by
  intro h h_buf
  unfold parseWithMlsLabel at h
  split at h
  · rename_i x' h_parse
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    grind [wf_of_parse]
  · simp at h

end MLS
