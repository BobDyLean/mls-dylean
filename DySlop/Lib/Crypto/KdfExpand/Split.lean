/-
  Port of `DY.Lib.Crypto.KdfExpand.Split`: split KDF.Expand usages.

  As in DY*, local KDF.Expand usages have the type of the global one
  (`KdfExpandUsage`, DY*'s `kdf_expand_crypto_usage`).
  Local KDF.Expand usages for the usage tags `tags` are `KdfExpandUsage.Local tags`
  (DY*'s `list (string & kdf_expand_crypto_usage)`), e.g.
    `def myUsage: KdfExpandUsage.Local ["MyTag"] := .single { getUsage := ..., getLabel := ..., getLabel_lemma := ... }`
  and are combined with `#combine into KdfExpandUsage from ...`.
-/

module

public import DySlop.EquationalTheories.KdfExpand
public import DySlop.Lib.Utils.SplitFunction
public meta import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction

namespace DySlop.KdfExpand

variable [ExecTraceTypes] [BytesFunctor]

/-- Port of `split_kdf_expand_usage_get_usage_params`. -/
@[expose, reducible]
public
def KdfExpandUsage.getUsageParams: SplitFunction.Params where
  Tag := String
  Input := Usage × Bytes
  RawInput := Usage × Bytes
  Output := Usage
  decode x :=
    if x.1.type = "KdfExpandKey" then
      some (x.1.tag, x)
    else
      none
  LocalFun _ := KdfExpandUsage
  applyLocal lusg x := KdfExpandUsage.getUsage (self := lusg) x.1 x.2
  default _ := Usage.nothing

/-- Port of `split_kdf_expand_usage_get_label_params`. -/
@[expose, reducible]
public
def KdfExpandUsage.getLabelParams: SplitFunction.Params where
  Tag := String
  Input := Usage × Label × Bytes
  RawInput := Usage × Label × Bytes
  Output := Label
  decode x :=
    if x.1.type = "KdfExpandKey" then
      some (x.1.tag, x)
    else
      none
  LocalFun _ := KdfExpandUsage
  applyLocal lusg x := KdfExpandUsage.getLabel (self := lusg) x.1 x.2.1 x.2.2
  default x := x.2.1

/-- Local KDF.Expand usages for the usage tags `tags`. -/
public
abbrev KdfExpandUsage.Local (tags: List String) := Locals (fun _: String => KdfExpandUsage) tags

/-- Port of `mk_global_kdf_expand_usage_get_usage`. -/
@[expose]
public
def KdfExpandUsage.Local.getUsage {tags: List String} (l: KdfExpandUsage.Local tags) (prkUsage: Usage) (info: Bytes): Usage :=
  SplitFunction.Params.Locals.toFun KdfExpandUsage.getUsageParams l (prkUsage, info)

/-- Port of `mk_global_kdf_expand_usage_get_label`. -/
@[expose]
public
def KdfExpandUsage.Local.getLabel {tags: List String} (l: KdfExpandUsage.Local tags) (prkUsage: Usage) (prkLabel: Label) (info: Bytes): Label :=
  SplitFunction.Params.Locals.toFun KdfExpandUsage.getLabelParams l (prkUsage, prkLabel, info)

/-- Port of `mk_global_kdf_expand_usage_get_label_lemma`. -/
public
theorem KdfExpandUsage.Local.getLabel_lemma
  {tags: List String} (l: KdfExpandUsage.Local tags)
  (tr: ExecTrace) (prkUsage: Usage) (prkLabel: Label) (info: Bytes)
  : prkUsage.type = "KdfExpandKey" →
    (l.getLabel prkUsage prkLabel info).canFlow prkLabel tr
:= by
  intro h_type
  apply SplitFunction.Params.mkGlobalFun_induction KdfExpandUsage.getLabelParams l.list (prkUsage, prkLabel, info)
    (fun (out: Label) => out.canFlow prkLabel tr)
  · intro tag lusg raw _ h_decode
    simp only [getLabelParams, Option.ite_none_right_eq_some, Option.some.injEq] at h_decode
    obtain ⟨h_type, -, rfl⟩ := h_decode
    exact KdfExpandUsage.getLabel_lemma (self := lusg) tr prkUsage prkLabel info h_type
  · exact canFlowRefl prkLabel tr

public
theorem KdfExpandUsage.Local.getUsage_single
  {tag: String} (lusg: KdfExpandUsage) (prkUsage: Usage) (info: Bytes)
  : prkUsage.type = "KdfExpandKey" →
    prkUsage.tag = tag →
    KdfExpandUsage.Local.getUsage (Locals.single (tag := tag) lusg) prkUsage info = KdfExpandUsage.getUsage (self := lusg) prkUsage info
:= by
  intro h_type h_tag
  subst h_tag
  exact SplitFunction.Params.Locals.toFun_single KdfExpandUsage.getUsageParams (tag := prkUsage.tag) lusg
    (prkUsage, info) (prkUsage, info) (by simp [h_type])

public
theorem KdfExpandUsage.Local.getLabel_single
  {tag: String} (lusg: KdfExpandUsage) (prkUsage: Usage) (prkLabel: Label) (info: Bytes)
  : prkUsage.type = "KdfExpandKey" →
    prkUsage.tag = tag →
    KdfExpandUsage.Local.getLabel (Locals.single (tag := tag) lusg) prkUsage prkLabel info = KdfExpandUsage.getLabel (self := lusg) prkUsage prkLabel info
:= by
  intro h_type h_tag
  subst h_tag
  exact SplitFunction.Params.Locals.toFun_single KdfExpandUsage.getLabelParams (tag := prkUsage.tag) lusg
    (prkUsage, prkLabel, info) (prkUsage, prkLabel, info) (by simp [h_type])

/-- Port of `has_kdf_expand_usage`. -/
public
class KdfExpandUsage.Has [KdfExpandUsage] {tags: List String} (l: KdfExpandUsage.Local tags): Prop where
  /-- Port of `has_kdf_expand_usage_get_usage`. -/
  getUsage_eq:
    ∀ (prkUsage: Usage) (info: Bytes),
      prkUsage.type = "KdfExpandKey" →
      prkUsage.tag ∈ tags →
      KdfExpandUsage.getUsage prkUsage info = l.getUsage prkUsage info
  /-- Port of `has_kdf_expand_usage_get_label`. -/
  getLabel_eq:
    ∀ (prkUsage: Usage) (prkLabel: Label) (info: Bytes),
      prkUsage.type = "KdfExpandKey" →
      prkUsage.tag ∈ tags →
      KdfExpandUsage.getLabel prkUsage prkLabel info = l.getLabel prkUsage prkLabel info

public
instance KdfExpandUsage.Has.ofHasStep
  [KdfExpandUsage] {tags1 tags2: List String} (l1: KdfExpandUsage.Local tags1) (l2: KdfExpandUsage.Local tags2)
  [HasStep l1 l2] [h: KdfExpandUsage.Has l2]
  : KdfExpandUsage.Has l1
where
  getUsage_eq prkUsage info h_type h_tag := by
    rw [h.getUsage_eq prkUsage info h_type (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitFunction.Params.Locals.toFun_of_hasStep KdfExpandUsage.getUsageParams l1 l2
      (prkUsage, info) prkUsage.tag (prkUsage, info) (by simp [h_type]) h_tag
  getLabel_eq prkUsage prkLabel info h_type h_tag := by
    rw [h.getLabel_eq prkUsage prkLabel info h_type (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitFunction.Params.Locals.toFun_of_hasStep KdfExpandUsage.getLabelParams l1 l2
      (prkUsage, prkLabel, info) prkUsage.tag (prkUsage, prkLabel, info) (by simp [h_type]) h_tag

/-- Port of `mk_kdf_expand_usage`. -/
@[expose, instance_reducible]
public
def KdfExpandUsage.ofLocal {tags: List String} (l: KdfExpandUsage.Local tags): KdfExpandUsage where
  getUsage := l.getUsage
  getLabel := l.getLabel
  getLabel_lemma := l.getLabel_lemma

/-- Port of `mk_kdf_expand_usage_correct`. -/
public
theorem KdfExpandUsage.ofLocal_has {tags: List String} (l: KdfExpandUsage.Local tags):
  letI := KdfExpandUsage.ofLocal l
  KdfExpandUsage.Has l
:= by
  letI := KdfExpandUsage.ofLocal l
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

end DySlop.KdfExpand

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* KdfExpandUsage $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.BytesFunctor])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `kdfExpandUsage
      localTypeName := ``DySlop.KdfExpand.KdfExpandUsage.Local
      mkTopLevel := DySlop.SplitFunction.Combine.globalInstances
        ``DySlop.KdfExpand.KdfExpandUsage ``DySlop.KdfExpand.KdfExpandUsage.ofLocal
        ``DySlop.KdfExpand.KdfExpandUsage.Has ``DySlop.KdfExpand.KdfExpandUsage.ofLocal_has
    }

end DY.Meta.CombineMacro
