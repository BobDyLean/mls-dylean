/-
  Port of `DY.Lib.Crypto.AEAD.Split`: split AEAD predicates.

  As in DY*, local AEAD predicates have the type of the global one (`AeadPred`, DY*'s `aead_crypto_predicate`),
  and the proof that a local AEAD predicate stays true when the trace grows is a `AeadPred.Later`
  (the `pred_later` field of DY*'s `aead_crypto_predicate`).
  Local AEAD predicates for the usage tags `tags` are `AeadPred.Local tags`
  (DY*'s `list (string & aead_crypto_predicate)`), e.g.
    `def myPred: AeadPred.Local ["MyTag"] := .single { pred := ... }`
    `theorem myPredProof [BytesInvariants]: AeadPred.LocalProof myPred := .single fun keyUsg ... => ...`
  and are combined with `#combine into AeadPred, AeadPredProof from ...`.
-/

module

public import DySlop.EquationalTheories.Aead
public import DySlop.Lib.Crypto.SplitPredicate
public meta import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction
open DySlop.SplitPredicate

namespace DySlop.Aead

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/--
  Port of the `pred_later` field of `aead_crypto_predicate`:
  the AEAD predicate `lpred` stays true when the trace grows
  (`AeadPredProof` for a AEAD predicate that is not the global instance).
-/
@[expose, reducible]
public
def AeadPred.Later [BytesInvariants] (lpred: AeadPred): Prop :=
  [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
  ∀ keyUsg key nonce msg ad tr1 tr2,
    key.WellFormed tr1 →
    nonce.WellFormed tr1 →
    msg.WellFormed tr1 →
    ad.WellFormed tr1 →
    tr1 ≤ tr2 →
    AeadPred.pred (self := lpred) keyUsg key nonce msg ad tr1 →
    AeadPred.pred (self := lpred) keyUsg key nonce msg ad tr2

/-- Port of `split_aead_predicate_params`. -/
@[expose, reducible]
public
def AeadPred.splitParams: SplitPredicate.Params where
  keyType := "AeadKey"
  Data := Bytes × Bytes × Bytes × Bytes
  LocalPred := AeadPred
  apply lpred := fun [BytesWellFormed] [GetUsage] [GetLabel] keyUsg data tr =>
    AeadPred.pred (self := lpred) keyUsg data.1 data.2.1 data.2.2.1 data.2.2.2 tr
  dataWellFormed := fun [BytesWellFormed] tr data =>
    data.1.WellFormed tr ∧ data.2.1.WellFormed tr ∧ data.2.2.1.WellFormed tr ∧ data.2.2.2.WellFormed tr
  LocalPredLater := fun [BytesInvariants] lpred =>
    lpred.Later
  apply_later := fun [BytesInvariants] _ h [BytesWellFormedLater] [GetUsageLater] [GetLabelLater] keyUsg data tr1 tr2 h_wf h_le h_pred =>
    h keyUsg data.1 data.2.1 data.2.2.1 data.2.2.2 tr1 tr2 h_wf.1 h_wf.2.1 h_wf.2.2.1 h_wf.2.2.2 h_le h_pred

/-- Local AEAD predicates for the usage tags `tags`. -/
public
abbrev AeadPred.Local (tags: List String) := AeadPred.splitParams.Local tags

/-- The AEAD predicate defined by local AEAD predicates. -/
@[expose]
public
def AeadPred.Local.pred {tags: List String} (l: AeadPred.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: Usage) (key nonce msg ad: Bytes) (tr: ProofTrace)
  : Prop
:=
  SplitPredicate.Params.Local.pred l keyUsg (key, nonce, msg, ad) tr

public
theorem AeadPred.Local.pred_single
  {tag: String} (lpred: AeadPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: Usage) (key nonce msg ad: Bytes) (tr: ProofTrace)
  : keyUsg.type = "AeadKey" →
    keyUsg.tag = tag →
    AeadPred.Local.pred (Locals.single (tag := tag) lpred) keyUsg key nonce msg ad tr = AeadPred.pred (self := lpred) keyUsg key nonce msg ad tr
:=
  SplitPredicate.Params.Local.pred_single AeadPred.splitParams (tag := tag) lpred keyUsg (key, nonce, msg, ad) tr

/-- Port of `has_aead_predicate`. -/
public
class AeadPred.Has [AeadPred] {tags: List String} (l: AeadPred.Local tags): Prop where
  pred_eq:
    ∀ [BytesWellFormed] [GetUsage] [GetLabel] (keyUsg: Usage) (key nonce msg ad: Bytes) (tr: ProofTrace),
      keyUsg.type = "AeadKey" →
      keyUsg.tag ∈ tags →
      AeadPred.pred keyUsg key nonce msg ad tr = l.pred keyUsg key nonce msg ad tr

public
instance AeadPred.Has.ofHasStep
  [AeadPred] {tags1 tags2: List String} (l1: AeadPred.Local tags1) (l2: AeadPred.Local tags2)
  [HasStep l1 l2] [h: AeadPred.Has l2]
  : AeadPred.Has l1
where
  pred_eq keyUsg key nonce msg ad tr h_type h_tag := by
    rw [h.pred_eq keyUsg key nonce msg ad tr h_type (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitPredicate.Params.Local.pred_of_hasStep _ l1 l2 keyUsg (key, nonce, msg, ad) tr h_type h_tag

/-- Port of `mk_aead_predicate`. -/
@[expose, instance_reducible]
public
def AeadPred.ofLocal {tags: List String} (l: AeadPred.Local tags): AeadPred where
  pred := l.pred

/-- Port of `mk_aead_predicate_correct`. -/
public
theorem AeadPred.ofLocal_has {tags: List String} (l: AeadPred.Local tags):
  letI := AeadPred.ofLocal l
  AeadPred.Has l
:= by
  letI := AeadPred.ofLocal l
  exact ⟨fun _ _ _ _ _ _ _ _ => rfl⟩

/-- Local AEAD predicates stay true when the trace grows. -/
public
abbrev AeadPred.LocalProof [BytesInvariants] {tags: List String} (l: AeadPred.Local tags): Prop :=
  SplitPredicate.Params.Local.Later l

public
theorem AeadPred.LocalProof.single
  [BytesInvariants] {tag: String} {lpred: AeadPred}
  : lpred.Later →
    AeadPred.LocalProof (Locals.single (tag := tag) lpred)
:=
  Locals.All.single (prop := fun _ lpred => AeadPred.splitParams.LocalPredLater lpred)

public
theorem AeadPred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (tags: List String) × AeadPred.Local tags)
  : (∀ id, AeadPred.LocalProof (ls id).2) →
    AeadPred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

/-- Port of the `pred_later` field of `mk_aead_predicate`. -/
public
theorem AeadPred.LocalProof.toGlobal
  [BytesInvariants] {tags: List String} {l: AeadPred.Local tags}
  : AeadPred.LocalProof l →
    letI := AeadPred.ofLocal l
    AeadPredProof
:= by
  intro h
  letI := AeadPred.ofLocal l
  exact ⟨fun keyUsg key nonce msg ad tr1 tr2 h_key h_nonce h_msg h_ad h_le =>
    SplitPredicate.Params.Local.Later.pred_later _ l h keyUsg (key, nonce, msg, ad) tr1 tr2 ⟨h_key, h_nonce, h_msg, h_ad⟩ h_le⟩

end DySlop.Aead

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* AeadPred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `aeadPred
      localTypeName := ``DySlop.Aead.AeadPred.Local
      mkTopLevel := DySlop.SplitFunction.Combine.globalInstances
        ``DySlop.Aead.AeadPred ``DySlop.Aead.AeadPred.ofLocal ``DySlop.Aead.AeadPred.Has ``DySlop.Aead.AeadPred.ofLocal_has
    }

macro_rules
  | `(command| #combine_one $options* AeadPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `aeadPredProof
      refereeName := `aeadPred
      localProofName := ``DySlop.Aead.AeadPred.LocalProof
      combineName := ``DySlop.Aead.AeadPred.LocalProof.combine
      mkTopLevel := DySlop.SplitFunction.Combine.globalProofInstance
        ``DySlop.Aead.AeadPredProof ``DySlop.Aead.AeadPred.LocalProof.toGlobal
    }

end DY.Meta.CombineMacro
