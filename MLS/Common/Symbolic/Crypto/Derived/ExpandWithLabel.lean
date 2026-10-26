module

public import MLS.Common.Symbolic.Crypto.Derived.MlsLabel
public import MLS.Symbolic.Code.Symbolic
public import DySlop.Lib.Crypto.KdfExpand.Split

/-!
Port of `MLS.Crypto.Derived.Symbolic.ExpandWithLabel`: split KDF.Expand usages for ExpandWithLabel,
and lemmas on `expandWithLabel`.

Local ExpandWithLabel usages for the labels `labels` are `ExpandWithLabelUsage.Local labels`, e.g.
  `def myUsage: ExpandWithLabelUsage.Local ["path"] := .single (.secret usg)`,
and are combined with `#combine into ExpandWithLabelUsage from ...`.
Unlike SignWithLabel, the KDF.Expand usage tag of the secret (e.g. `"MLS.PathSecret"`) is a parameter:
the local KDF.Expand usage defined by local ExpandWithLabel usages `l` is `ExpandWithLabelUsage.toKdfExpandUsage tag l`,
to be combined into `KdfExpandUsage`, and `ExpandWithLabelUsage.Has.ofToKdfExpandUsage` derives `ExpandWithLabelUsage.Has tag l`.

Port-specific differences: the tags are the labels without the prefix `"MLS 1.0 "` (see `parseWithMlsLabel`).
-/

namespace MLS

open DY
open DySlop DySlop.KdfExpand DySlop.SplitFunction
open Comparse

section Local

variable [BytesFunctor] [ExecTraceTypes]

/--
  Port of `expandwithlabel_crypto_usage`.
  MLS* requires `KdfExpandKey? prk_usage`; here, the functions are defined on all usages.
-/
public
structure ExpandWithLabelUsage where
  getUsage (prkUsage: Usage) (context: Bytes) (length: Nat): Usage
  getLabel (prkUsage: Usage) (prkLabel: Label) (context: Bytes) (length: Nat): Label
  getLabel_lemma (tr: ExecTrace) (prkUsage: Usage) (prkLabel: Label) (context: Bytes) (length: Nat)
    : prkUsage.type = "KdfExpandKey" →
      (getLabel prkUsage prkLabel context length).canFlow prkLabel tr

/-- Port of `default_expandwithlabel_crypto_usage`. -/
@[expose]
public
def ExpandWithLabelUsage.default: ExpandWithLabelUsage where
  getUsage _ _ _ := Usage.nothing
  getLabel _ prkLabel _ _ := prkLabel
  getLabel_lemma := by grind

/-- Port of `mk_secret_expandwithlabel_usage`. -/
@[expose]
public
def ExpandWithLabelUsage.secret (usg: Usage): ExpandWithLabelUsage where
  getUsage _ _ _ := usg
  getLabel _ prkLabel _ _ := prkLabel
  getLabel_lemma := by grind

/-- Port of `mk_public_expandwithlabel_usage`. -/
@[expose]
public
def ExpandWithLabelUsage.public (usg: Usage): ExpandWithLabelUsage where
  getUsage _ _ _ := usg
  getLabel _ _ _ _ := Label.pub
  getLabel_lemma := by grind

/-- Local ExpandWithLabel usages for the labels `labels` (MLS*'s `list (valid_label & expandwithlabel_crypto_usage)`). -/
public
abbrev ExpandWithLabelUsage.Local (labels: List String) := Locals (fun _: String => ExpandWithLabelUsage) labels

end Local

section Code

variable [HasSymbolicBytes]

public
theorem expandWithLabel_eq_success (secret: Bytes) (label: String) (context: Bytes) (len: Nat) (res: Bytes)
  : expandWithLabel secret label context len = .success res →
    ∃ kdfLabel: KdfLabel Bytes,
      kdfLabel.label.val.val = "MLS 1.0 " ++ label ∧
      kdfLabel.context.val = context ∧
      kdfLabel.length.toNat = len ∧
      res = DySlop.KdfExpand.kdfExpand secret (serializeNE KdfLabel.mf kdfLabel) len
:= by
  simp only [expandWithLabel, Result.bind_eq_success, mkUInt16_eq_success, mkMlsBytes_eq_success,
    getMlsLabel_eq_success, cryptoBytesBytes_kdfExpand]
  rintro ⟨length, ⟨h_len, rfl⟩, mlsContext, rfl, mlsLabel, h_label, h⟩
  split at h
  · simp [Result.internalFailure] at h
  · refine ⟨{ length := len.toUInt16, label := mlsLabel, context := mlsContext }, h_label.symm, rfl, ?_, ?_⟩
    · simp; omega
    · simp_all

end Code

section SplitUsage

variable [HasSymbolicBytes] [ExecTraceTypes]

/-- Port of `split_expandwithlabel_get_usage_params`. -/
@[expose, reducible]
public
def ExpandWithLabelUsage.getUsageParams: SplitFunction.Params where
  Tag := String
  -- the usage of the secret, the info
  Input := Usage × Bytes
  -- the usage of the secret, the context, the length
  RawInput := Usage × Bytes × Nat
  Output := Usage
  decode x :=
    match parseWithMlsLabel KdfLabel.mf KdfLabel.label x.2 with
    | some (label, kdfLabel) => some (label, (x.1, kdfLabel.context.val, kdfLabel.length.toNat))
    | none => none
  LocalFun _ := ExpandWithLabelUsage
  applyLocal lusg x := lusg.getUsage x.1 x.2.1 x.2.2
  default _ := Usage.nothing

/-- Port of `split_expandwithlabel_get_label_params`. -/
@[expose, reducible]
public
def ExpandWithLabelUsage.getLabelParams: SplitFunction.Params where
  Tag := String
  -- the usage and label of the secret, the info
  Input := Usage × Label × Bytes
  -- the usage and label of the secret, the context, the length
  RawInput := Usage × Label × Bytes × Nat
  Output := Label
  decode x :=
    match parseWithMlsLabel KdfLabel.mf KdfLabel.label x.2.2 with
    | some (label, kdfLabel) => some (label, (x.1, x.2.1, kdfLabel.context.val, kdfLabel.length.toNat))
    | none => none
  LocalFun _ := ExpandWithLabelUsage
  applyLocal lusg x := lusg.getLabel x.1 x.2.1 x.2.2.1 x.2.2.2
  default x := x.2.1

theorem ExpandWithLabelUsage.getUsageParams_decode (prkUsage: Usage) (info: Bytes) (label: String) (kdfLabel: KdfLabel Bytes)
  : parseWithMlsLabel KdfLabel.mf KdfLabel.label info = some (label, kdfLabel) →
    ExpandWithLabelUsage.getUsageParams.decode (prkUsage, info) =
      some (label, (prkUsage, kdfLabel.context.val, kdfLabel.length.toNat))
:= by
  intro h
  simp [h]

theorem ExpandWithLabelUsage.getLabelParams_decode (prkUsage: Usage) (prkLabel: Label) (info: Bytes) (label: String) (kdfLabel: KdfLabel Bytes)
  : parseWithMlsLabel KdfLabel.mf KdfLabel.label info = some (label, kdfLabel) →
    ExpandWithLabelUsage.getLabelParams.decode (prkUsage, prkLabel, info) =
      some (label, (prkUsage, prkLabel, kdfLabel.context.val, kdfLabel.length.toNat))
:= by
  intro h
  simp [h]

/-- The usage given by the local ExpandWithLabel usage for the label `label`. -/
public
abbrev ExpandWithLabelUsage.Local.getUsage {labels: List String} (l: ExpandWithLabelUsage.Local labels)
  (label: String) (prkUsage: Usage) (context: Bytes) (length: Nat): Usage
:=
  Params.Locals.apply ExpandWithLabelUsage.getUsageParams l label (prkUsage, context, length) Usage.nothing

/-- The label given by the local ExpandWithLabel usage for the label `label`. -/
public
abbrev ExpandWithLabelUsage.Local.getLabel {labels: List String} (l: ExpandWithLabelUsage.Local labels)
  (label: String) (prkUsage: Usage) (prkLabel: Label) (context: Bytes) (length: Nat): Label
:=
  Params.Locals.apply ExpandWithLabelUsage.getLabelParams l label (prkUsage, prkLabel, context, length) prkLabel

/-- Port of `mk_kdf_expand_mls_usage`: the KDF.Expand usage defined by local ExpandWithLabel usages. -/
@[expose, instance_reducible]
public
def ExpandWithLabelUsage.ofLocal {labels: List String} (l: ExpandWithLabelUsage.Local labels): KdfExpandUsage where
  getUsage prkUsage info := Params.Locals.toFun ExpandWithLabelUsage.getUsageParams l (prkUsage, info)
  getLabel prkUsage prkLabel info := Params.Locals.toFun ExpandWithLabelUsage.getLabelParams l (prkUsage, prkLabel, info)
  getLabel_lemma tr prkUsage prkLabel info h := by
    cases h_decode: parseWithMlsLabel KdfLabel.mf KdfLabel.label info with
    | none =>
      rw [Params.Locals.toFun_eq_default ExpandWithLabelUsage.getLabelParams l _ (by simp [h_decode])]
      exact canFlowRefl _ _
    | some x =>
      obtain ⟨label, kdfLabel⟩ := x
      rw [Params.Locals.toFun_eq ExpandWithLabelUsage.getLabelParams l _ label _
        (ExpandWithLabelUsage.getLabelParams_decode prkUsage prkLabel info label kdfLabel h_decode)]
      let raw := (prkUsage, prkLabel, kdfLabel.context.val, kdfLabel.length.toNat)
      apply Params.Locals.apply_rel ExpandWithLabelUsage.getLabelParams l label raw raw prkLabel prkLabel
        (fun out _ => out.canFlow prkLabel tr)
      · intro x _
        exact x.2.getLabel_lemma tr prkUsage prkLabel _ _ h
      · exact canFlowRefl _ _

/--
  Port of `has_expandwithlabel_usage`:
  the KDF.Expand usage `kusg` coincides with the local ExpandWithLabel usages `l` on their labels.
-/
@[expose]
public
def ExpandWithLabelUsage.HasLocal (kusg: KdfExpandUsage) {labels: List String} (l: ExpandWithLabelUsage.Local labels): Prop :=
  ExpandWithLabelUsage.getUsageParams.HasLocal (fun x => kusg.getUsage x.1 x.2) l ∧
  ExpandWithLabelUsage.getLabelParams.HasLocal (fun x => kusg.getLabel x.1 x.2.1 x.2.2) l

/-- Port of `mk_kdf_expand_mls_usage_correct`. -/
public
theorem ExpandWithLabelUsage.ofLocal_hasLocal {labels: List String} (l: ExpandWithLabelUsage.Local labels)
  : ExpandWithLabelUsage.HasLocal (ExpandWithLabelUsage.ofLocal l) l
:=
  ⟨Params.Locals.toFun_hasLocal ExpandWithLabelUsage.getUsageParams l, Params.Locals.toFun_hasLocal ExpandWithLabelUsage.getLabelParams l⟩

/-- The local KDF.Expand usage for the usage tag `tag`, defined by local ExpandWithLabel usages. -/
public
abbrev ExpandWithLabelUsage.toKdfExpandUsage (tag: String) {labels: List String} (l: ExpandWithLabelUsage.Local labels)
  : KdfExpandUsage.Local [tag]
:=
  Locals.single (ExpandWithLabelUsage.ofLocal l)

/-- Port of `has_mls_expandwithlabel_usage`. -/
public
class ExpandWithLabelUsage.Has [kdfExpandUsage: KdfExpandUsage] (tag: String) {labels: List String} (l: ExpandWithLabelUsage.Local labels): Prop where
  pf: ∃ mlsKdfExpandUsage: KdfExpandUsage,
    -- the global KDF.Expand usage is explicit, otherwise `mlsKdfExpandUsage` would be used as the `KdfExpandUsage` instance
    @KdfExpandUsage.Has _ _ kdfExpandUsage _ (Locals.single (tag := tag) mlsKdfExpandUsage) ∧
    ExpandWithLabelUsage.HasLocal mlsKdfExpandUsage l

public
instance ExpandWithLabelUsage.Has.ofHasStep
  [KdfExpandUsage] (tag: String) {labels1 labels2: List String}
  (l1: ExpandWithLabelUsage.Local labels1) (l2: ExpandWithLabelUsage.Local labels2)
  [HasStep l1 l2] [h: ExpandWithLabelUsage.Has tag l2]
  : ExpandWithLabelUsage.Has tag l1
where
  pf := by
    obtain ⟨mlsKdfExpandUsage, h_kdf, h_getUsage, h_getLabel⟩ := h.pf
    exact ⟨mlsKdfExpandUsage, h_kdf, Params.HasLocal.of_hasStep ExpandWithLabelUsage.getUsageParams _ l1 l2 h_getUsage, Params.HasLocal.of_hasStep ExpandWithLabelUsage.getLabelParams _ l1 l2 h_getLabel⟩

public
theorem ExpandWithLabelUsage.Has.ofToKdfExpandUsage
  [KdfExpandUsage] (tag: String) {labels: List String} (l: ExpandWithLabelUsage.Local labels)
  [h: KdfExpandUsage.Has (ExpandWithLabelUsage.toKdfExpandUsage tag l)]
  : ExpandWithLabelUsage.Has tag l
:=
  ⟨⟨ExpandWithLabelUsage.ofLocal l, h, ExpandWithLabelUsage.ofLocal_hasLocal l⟩⟩

/-- The global KDF.Expand usage on a KDF label, given the local ExpandWithLabel usages. -/
public
theorem ExpandWithLabelUsage.Has.kdfExpandUsage_eq
  [KdfExpandUsage] {labels: List String} (l: ExpandWithLabelUsage.Local labels) (tag: String) [h: ExpandWithLabelUsage.Has tag l]
  (prkUsage: Usage) (prkLabel: Label) (label: String) (kdfLabel: KdfLabel Bytes)
  : kdfLabel.label.val.val = "MLS 1.0 " ++ label →
    prkUsage.type = "KdfExpandKey" →
    prkUsage.tag = tag →
    label ∈ labels →
    KdfExpandUsage.getUsage prkUsage (serializeNE KdfLabel.mf kdfLabel) =
      l.getUsage label prkUsage kdfLabel.context.val kdfLabel.length.toNat ∧
    KdfExpandUsage.getLabel prkUsage prkLabel (serializeNE KdfLabel.mf kdfLabel) =
      l.getLabel label prkUsage prkLabel kdfLabel.context.val kdfLabel.length.toNat
:= by
  intro h_label h_type h_tag h_mem
  obtain ⟨mlsKdfExpandUsage, h_kdf, h_getUsage, h_getLabel⟩ := h.pf
  have h_decode := parseWithMlsLabel_serializeNE KdfLabel.mf KdfLabel.label kdfLabel label h_label
  rw [h_kdf.getUsage_eq _ _ h_type (by simp [h_tag]), h_kdf.getLabel_eq _ _ _ h_type (by simp [h_tag]),
    KdfExpandUsage.Local.getUsage_single _ _ _ h_type h_tag, KdfExpandUsage.Local.getLabel_single _ _ _ _ h_type h_tag]
  exact ⟨h_getUsage _ label _ (ExpandWithLabelUsage.getUsageParams_decode _ _ label kdfLabel h_decode) h_mem,
    h_getLabel _ label _ (ExpandWithLabelUsage.getLabelParams_decode _ _ _ label kdfLabel h_decode) h_mem⟩

end SplitUsage

section Proofs

variable [HasSymbolicInvariants]

/-- Port of `expand_with_label_lemma` (and of `bytes_invariant_expand_with_label`, `has_usage_expand_with_label`, `get_label_expand_with_label`). -/
public
theorem expandWithLabel.Invariant
  {labels: List String} (l: ExpandWithLabelUsage.Local labels) (tag: String) [ExpandWithLabelUsage.Has tag l]
  (tr: ProofTrace) (secret: Bytes) (secretUsage: Usage) (label: String) (context: Bytes) (len: Nat) (res: Bytes)
  : expandWithLabel secret label context len = .success res →
    secret.Invariant tr →
    context.Invariant tr →
    secret.HasUsage secretUsage tr →
    secretUsage.type = "KdfExpandKey" →
    secretUsage.tag = tag →
    label ∈ labels →
    res.Invariant tr ∧
    res.HasUsage (l.getUsage label secretUsage context len) tr ∧
    (res.label tr).equivalent (l.getLabel label secretUsage (secret.label tr) context len) tr.erase
:= by
  intro h_expand h_secret h_context h_usg h_type h_tag h_label
  obtain ⟨kdfLabel, h_mlsLabel, rfl, rfl, rfl⟩ := expandWithLabel_eq_success secret label _ _ res h_expand
  have h_info := (pred_serializeNE_iff KdfLabel.mf (Bytes.Invariant · tr) kdfLabel).2 (by simpa using h_context)
  have := ExpandWithLabelUsage.Has.kdfExpandUsage_eq l tag secretUsage (secret.label tr) label kdfLabel h_mlsLabel h_type h_tag h_label
  have := kdfExpand.HasUsage secret secretUsage (serializeNE KdfLabel.mf kdfLabel) kdfLabel.length.toNat tr h_usg h_type
  have := kdfExpand.label_equivalent secret secretUsage (serializeNE KdfLabel.mf kdfLabel) kdfLabel.length.toNat tr h_usg h_type
  have := kdfExpand.Invariant secret secretUsage (serializeNE KdfLabel.mf kdfLabel) kdfLabel.length.toNat tr h_secret h_info h_usg h_type
  grind

end Proofs

end MLS

/-! ## Support for the `#combine` macro -/

namespace DY.Meta.CombineMacro

/-- `#combine into ExpandWithLabelUsage from A, B` combines `A.expandWithLabelUsage` and `B.expandWithLabelUsage`. -/
macro_rules
  | `(command| #combine_one $options* ExpandWithLabelUsage $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `expandWithLabelUsage
      localTypeName := ``MLS.ExpandWithLabelUsage.Local
      mkTopLevel := fun _ => pure #[]
    }

end DY.Meta.CombineMacro
