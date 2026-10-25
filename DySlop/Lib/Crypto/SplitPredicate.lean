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

/-- Port of `split_crypto_predicate_parameters`. -/
public
structure Params where
  /--
    The type of the key usages, e.g. `"SigKey"`.
    DY*'s `key_usage_t` and `get_usage`: the tag of a key usage `usg` with `usg.type = keyType` is `usg.tag`.
  -/
  keyType: String
  Data: Type
  LocalPred: Type
  /-- DY*'s `apply_local_pred`. -/
  apply: LocalPred → [BytesWellFormed] → [GetUsage] → [GetLabel] → Usage → Data → ProofTrace → Prop
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
  Input := PredInstances × Usage × C.Data × ProofTrace
  RawInput := PredInstances × Usage × C.Data × ProofTrace
  Output := Prop
  decode x :=
    if x.2.1.type = C.keyType then
      some (x.2.1.tag, x)
    else
      none
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
  (keyUsg: Usage) (data: C.Data) (tr: ProofTrace)
  : Prop
:=
  SplitFunction.Params.Locals.toFun C.toSplitFunctionParams l (⟨⟩, keyUsg, data, tr)

public
theorem Local.pred_single
  {tag: String} (lpred: C.LocalPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: Usage) (data: C.Data) (tr: ProofTrace)
  : keyUsg.type = C.keyType →
    keyUsg.tag = tag →
    Local.pred (C := C) (Locals.single (tag := tag) lpred) keyUsg data tr =
    C.apply lpred keyUsg data tr
:= by
  intro h_type h_tag
  subst h_tag
  unfold Local.pred
  exact SplitFunction.Params.Locals.toFun_single C.toSplitFunctionParams (tag := keyUsg.tag) lpred
    (⟨⟩, keyUsg, data, tr) (⟨⟩, keyUsg, data, tr) (by simp [toSplitFunctionParams, h_type])

public
theorem Local.pred_of_hasStep
  {tags1 tags2: List String} (l1: C.Local tags1) (l2: C.Local tags2) [HasStep l1 l2]
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: Usage) (data: C.Data) (tr: ProofTrace)
  : keyUsg.type = C.keyType →
    keyUsg.tag ∈ tags1 →
    l2.pred keyUsg data tr = l1.pred keyUsg data tr
:= by
  intro h_type h_tag
  unfold Local.pred
  exact SplitFunction.Params.Locals.toFun_of_hasStep C.toSplitFunctionParams l1 l2
    (⟨⟩, keyUsg, data, tr) keyUsg.tag (⟨⟩, keyUsg, data, tr) (by simp [toSplitFunctionParams, h_type]) h_tag

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
  apply SplitFunction.Params.mkGlobalFun_induction C.toSplitFunctionParams l.list (⟨⟩, keyUsg, data, tr1) (fun (out: Prop) => out → l.pred keyUsg data tr2)
  · intro tag lpred raw h_find h_decode h_pred
    simp only [toSplitFunctionParams, Option.ite_none_right_eq_some, Option.some.injEq] at h_decode
    obtain ⟨h_type, rfl, rfl⟩ := h_decode
    have := C.apply_later lpred (h _ (mem_of_findLocalFun_eq_some _ _ _ h_find)) keyUsg data tr1 tr2 h_wf h_le h_pred
    unfold Local.pred SplitFunction.Params.Locals.toFun
    rw [SplitFunction.Params.mkGlobalFun_of_findLocalFun _ l.list _ lpred (⟨⟩, keyUsg, data, tr2)]
    · exact this
    · simp [toSplitFunctionParams, h_type]
    · exact h_find
  · simp

end Params

end DySlop.SplitPredicate
