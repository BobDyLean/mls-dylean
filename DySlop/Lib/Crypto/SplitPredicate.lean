/-
  Port of `DY.Lib.Crypto.SplitPredicate`: create a global cryptographic predicate from several independent local predicates.

  This specializes `DySlop.Lib.Utils.SplitFunction` to cryptographic predicates
  where the tag is the tag of the key usage, and the predicate stays true when the trace grows.

  Differences with DY*: as for the equational theories, a cryptographic predicate is split in two
  (e.g. `SignPred` and `SignPredProof`), because the proof that it stays true when the trace grows
  depends on the bytes invariants, which depend on the predicate.
  Hence `apply_local_pred_later` becomes `LocalPredLater` (the proof that a local predicate stays true)
  and `apply_later` (how to use it).
-/

module

public import DY.Bytes
public import DY.Trace
public import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction

namespace DySlop.SplitPredicate

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/-- The instances that cryptographic predicates depend on. -/
public
structure PredInstances where
  [wf: BytesWellFormed]
  [usage: GetUsage]
  [label: GetLabel]

/--
  DY*'s `get_usage` for key usages of type `keyType` (e.g. `sk_usage:usage{SigKey? sk_usage}`):
  the tag of the usage, or `none` for usages of another type.
-/
@[expose, reducible]
public
def usageTag (keyType: String) (usg: Usage): Option String :=
  if usg.type = keyType then some usg.tag else none

omit [ExecTraceTypes] [ProofTraceTypes] in
public
theorem usageTag_eq_some {keyType: String} {usg: Usage} {tag: String}
  : usg.type = keyType →
    usg.tag = tag →
    usageTag keyType usg = some tag
:= by
  intro h_type h_tag
  simp [usageTag, h_type, h_tag]

/-- Port of `split_crypto_predicate_parameters`. -/
public
structure Params where
  /-- DY*'s `key_usage_t`. -/
  KeyUsage: Type
  /--
    DY*'s `get_usage`: the tag of a key usage.
    It is `none` on the key usages excluded by the refinement of DY*'s `key_usage_t` (see `usageTag`).
  -/
  getTag: KeyUsage → Option String
  Data: Type
  LocalPred: Type
  /-- DY*'s `apply_local_pred`. -/
  apply: LocalPred → [BytesWellFormed] → [GetUsage] → [GetLabel] → KeyUsage → Data → ProofTrace → Prop
  /-- DY*'s `data_well_formed`. -/
  dataWellFormed: [BytesWellFormed] → ProofTrace → Data → Prop
  /-- The proof that a local predicate stays true when the trace grows. -/
  LocalPredLater: [BytesInvariants] → LocalPred → Prop
  /-- DY*'s `apply_local_pred_later`. -/
  apply_later:
    [BytesInvariants] → ∀ lpred, LocalPredLater lpred →
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ keyUsg data tr1 tr2,
      dataWellFormed tr1 data →
      tr1 ≤ tr2 →
      apply lpred keyUsg data tr1 →
      apply lpred keyUsg data tr2

namespace Params

variable (C: Params)

/-- Port of `split_crypto_predicate_parameters_to_split_function_parameters`. -/
@[expose, reducible]
public
def toSplitFunctionParams: SplitFunction.Params where
  Tag := String
  Input := PredInstances × C.KeyUsage × C.Data × ProofTrace
  RawInput := PredInstances × C.KeyUsage × C.Data × ProofTrace
  Output := Prop
  decode x :=
    match C.getTag x.2.1 with
    | some tag => some (tag, x)
    | none => none
  LocalFun _ := C.LocalPred
  applyLocal lpred x := @C.apply lpred x.1.wf x.1.usage x.1.label x.2.1 x.2.2.1 x.2.2.2
  default _ := False

/-- Local cryptographic predicates for the usage tags `tags`. -/
public
abbrev Local (tags: List String) := Locals (fun _: String => C.LocalPred) tags

/-- The predicate defined by local cryptographic predicates. -/
@[expose]
public
def Local.pred {C: Params} {tags: List String} (l: C.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: C.KeyUsage) (data: C.Data) (tr: ProofTrace)
  : Prop
:=
  SplitFunction.Params.Locals.toFun C.toSplitFunctionParams l (⟨⟩, keyUsg, data, tr)

public
theorem decode_eq_some
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: C.KeyUsage) (data: C.Data) (tr: ProofTrace) (tag: String)
  : C.getTag keyUsg = some tag →
    C.toSplitFunctionParams.decode (⟨⟩, keyUsg, data, tr) = some (tag, (⟨⟩, keyUsg, data, tr))
:= by
  intro h
  simp [h]

public
theorem Local.pred_single
  {tag: String} (lpred: C.LocalPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: C.KeyUsage) (data: C.Data) (tr: ProofTrace)
  : C.getTag keyUsg = some tag →
    Local.pred (C := C) (Locals.single (tag := tag) lpred) keyUsg data tr =
    C.apply lpred keyUsg data tr
:= by
  intro h
  exact SplitFunction.Params.Locals.toFun_single C.toSplitFunctionParams lpred _ _ (C.decode_eq_some keyUsg data tr tag h)

public
theorem Local.pred_of_hasStep
  {tags1 tags2: List String} (l1: C.Local tags1) (l2: C.Local tags2) [HasStep l1 l2]
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: C.KeyUsage) (data: C.Data) (tr: ProofTrace) (tag: String)
  : C.getTag keyUsg = some tag →
    tag ∈ tags1 →
    l2.pred keyUsg data tr = l1.pred keyUsg data tr
:= by
  intro h h_tag
  exact SplitFunction.Params.Locals.toFun_of_hasStep C.toSplitFunctionParams l1 l2 _ tag _ (C.decode_eq_some keyUsg data tr tag h) h_tag

/-- The local predicates stay true when the trace grows. -/
public
abbrev Local.Later [BytesInvariants] {C: Params} {tags: List String} (l: C.Local tags): Prop :=
  l.All (fun _ lpred => C.LocalPredLater lpred)

/-- Port of `mk_global_crypto_predicate_later`. -/
public
theorem Local.Later.pred_later
  [BytesInvariants] {tags: List String} (l: C.Local tags)
  : Local.Later l →
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ keyUsg data tr1 tr2,
      C.dataWellFormed tr1 data →
      tr1 ≤ tr2 →
      l.pred keyUsg data tr1 →
      l.pred keyUsg data tr2
:= by
  intro h _ _ _ keyUsg data tr1 tr2 h_wf h_le
  unfold Local.pred
  cases h_tag: C.getTag keyUsg with
  | none => simp [SplitFunction.Params.Locals.toFun_eq_default, h_tag]
  | some tag =>
    rw [SplitFunction.Params.Locals.toFun_eq C.toSplitFunctionParams l _ tag _ (C.decode_eq_some keyUsg data tr1 tag h_tag),
      SplitFunction.Params.Locals.toFun_eq C.toSplitFunctionParams l _ tag _ (C.decode_eq_some keyUsg data tr2 tag h_tag)]
    apply SplitFunction.Params.Locals.apply_rel C.toSplitFunctionParams l tag _ _ _ _ (fun p1 p2 => p1 → p2)
    · intro x h_mem
      exact C.apply_later x.2 (h x h_mem) keyUsg data tr1 tr2 h_wf h_le
    · exact id

end Params

end DySlop.SplitPredicate
