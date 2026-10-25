/-
  Port of `DY.Lib.Crypto.Signature.Split`: split sign predicates.

  As in DY*, local sign predicates have the type of the global one (`SignPred`, DY*'s `sign_crypto_predicate`),
  and the proof that a local sign predicate stays true when the trace grows is a `SignPred.Later`
  (the `pred_later` field of DY*'s `sign_crypto_predicate`).
  Local sign predicates for the usage tags `tags` are `SignPred.Local tags`
  (DY*'s `list (string & sign_crypto_predicate)`), e.g.
    `def myPred: SignPred.Local ["MyTag"] := .single { pred := ... }`
    `theorem myPredProof [BytesInvariants]: SignPred.LocalProof myPred := .single fun skUsg ... => ...`
  and are combined with `#combine into SignPred, SignPredProof from ...`.
-/

module

public import DySlop.EquationalTheories.Signature
public import DySlop.Lib.Crypto.SplitPredicate
public meta import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction
open DySlop.SplitPredicate

namespace DySlop.Signature

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/--
  Port of the `pred_later` field of `sign_crypto_predicate`:
  the sign predicate `lpred` stays true when the trace grows
  (`SignPredProof` for a sign predicate that is not the global instance).
-/
@[expose, reducible]
public
def SignPred.Later [BytesInvariants] (lpred: SignPred): Prop :=
  [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
  ∀ skUsg vk msg tr1 tr2,
    vk.WellFormed tr1 →
    msg.WellFormed tr1 →
    tr1 ≤ tr2 →
    SignPred.pred (self := lpred) skUsg vk msg tr1 →
    SignPred.pred (self := lpred) skUsg vk msg tr2

/-- Port of `split_sign_predicate_params`. -/
@[expose, reducible]
public
def SignPred.splitParams: SplitPredicate.Params where
  keyType := "SigKey"
  Data := Bytes × Bytes
  LocalPred := SignPred
  apply lpred := fun [BytesWellFormed] [GetUsage] [GetLabel] skUsg data tr =>
    SignPred.pred (self := lpred) skUsg data.1 data.2 tr
  dataWellFormed := fun [BytesWellFormed] tr data =>
    data.1.WellFormed tr ∧ data.2.WellFormed tr
  LocalPredLater := fun [BytesInvariants] lpred =>
    lpred.Later
  apply_later := fun [BytesInvariants] _ h [BytesWellFormedLater] [GetUsageLater] [GetLabelLater] skUsg data tr1 tr2 h_wf h_le h_pred =>
    h skUsg data.1 data.2 tr1 tr2 h_wf.1 h_wf.2 h_le h_pred

/-- Local sign predicates for the usage tags `tags`. -/
public
abbrev SignPred.Local (tags: List String) := SignPred.splitParams.Local tags

/-- The sign predicate defined by local sign predicates. -/
@[expose]
public
def SignPred.Local.pred {tags: List String} (l: SignPred.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (vk msg: Bytes) (tr: ProofTrace)
  : Prop
:=
  SplitPredicate.Params.Local.pred l skUsg (vk, msg) tr

public
theorem SignPred.Local.pred_single
  {tag: String} (lpred: SignPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (vk msg: Bytes) (tr: ProofTrace)
  : skUsg.type = "SigKey" →
    skUsg.tag = tag →
    SignPred.Local.pred (Locals.single (tag := tag) lpred) skUsg vk msg tr = SignPred.pred (self := lpred) skUsg vk msg tr
:=
  SplitPredicate.Params.Local.pred_single SignPred.splitParams (tag := tag) lpred skUsg (vk, msg) tr

/-- Port of `has_sign_predicate`. -/
public
class SignPred.Has [SignPred] {tags: List String} (l: SignPred.Local tags): Prop where
  pred_eq:
    ∀ [BytesWellFormed] [GetUsage] [GetLabel] (skUsg: Usage) (vk msg: Bytes) (tr: ProofTrace),
      skUsg.type = "SigKey" →
      skUsg.tag ∈ tags →
      SignPred.pred skUsg vk msg tr = l.pred skUsg vk msg tr

public
instance SignPred.Has.ofHasStep
  [SignPred] {tags1 tags2: List String} (l1: SignPred.Local tags1) (l2: SignPred.Local tags2)
  [HasStep l1 l2] [h: SignPred.Has l2]
  : SignPred.Has l1
where
  pred_eq skUsg vk msg tr h_type h_tag := by
    rw [h.pred_eq skUsg vk msg tr h_type (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitPredicate.Params.Local.pred_of_hasStep _ l1 l2 skUsg (vk, msg) tr h_type h_tag

/-- Port of `mk_sign_predicate`. -/
@[expose, instance_reducible]
public
def SignPred.ofLocal {tags: List String} (l: SignPred.Local tags): SignPred where
  pred := l.pred

/-- Port of `mk_sign_predicate_correct`. -/
public
theorem SignPred.ofLocal_has {tags: List String} (l: SignPred.Local tags):
  letI := SignPred.ofLocal l
  SignPred.Has l
:= by
  letI := SignPred.ofLocal l
  exact ⟨fun _ _ _ _ _ _ => rfl⟩

/-- Local sign predicates stay true when the trace grows. -/
public
abbrev SignPred.LocalProof [BytesInvariants] {tags: List String} (l: SignPred.Local tags): Prop :=
  SplitPredicate.Params.Local.Later l

public
theorem SignPred.LocalProof.single
  [BytesInvariants] {tag: String} {lpred: SignPred}
  : lpred.Later →
    SignPred.LocalProof (Locals.single (tag := tag) lpred)
:=
  Locals.All.single (prop := fun _ lpred => SignPred.splitParams.LocalPredLater lpred)

public
theorem SignPred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (tags: List String) × SignPred.Local tags)
  : (∀ id, SignPred.LocalProof (ls id).2) →
    SignPred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

/-- Port of the `pred_later` field of `mk_sign_predicate`. -/
public
theorem SignPred.LocalProof.toGlobal
  [BytesInvariants] {tags: List String} {l: SignPred.Local tags}
  : SignPred.LocalProof l →
    letI := SignPred.ofLocal l
    SignPredProof
:= by
  intro h
  letI := SignPred.ofLocal l
  exact ⟨fun skUsg vk msg tr1 tr2 h_vk h_msg h_le =>
    SplitPredicate.Params.Local.Later.pred_later _ l h skUsg (vk, msg) tr1 tr2 ⟨h_vk, h_msg⟩ h_le⟩

end DySlop.Signature

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* SignPred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `signPred
      localTypeName := ``DySlop.Signature.SignPred.Local
      mkTopLevel := DySlop.SplitFunction.Combine.globalInstances
        ``DySlop.Signature.SignPred ``DySlop.Signature.SignPred.ofLocal ``DySlop.Signature.SignPred.Has ``DySlop.Signature.SignPred.ofLocal_has
    }

macro_rules
  | `(command| #combine_one $options* SignPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `signPredProof
      refereeName := `signPred
      localProofName := ``DySlop.Signature.SignPred.LocalProof
      combineName := ``DySlop.Signature.SignPred.LocalProof.combine
      mkTopLevel := DySlop.SplitFunction.Combine.globalProofInstance
        ``DySlop.Signature.SignPredProof ``DySlop.Signature.SignPred.LocalProof.toGlobal
    }

end DY.Meta.CombineMacro
