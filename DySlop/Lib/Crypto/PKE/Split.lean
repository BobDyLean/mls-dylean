/-
  Port of `DY.Lib.Crypto.PKE.Split`: split PKE predicates.

  As in DY*, local PKE predicates have the type of the global one (`PkePred`, DY*'s `pke_crypto_predicate`),
  and the proof that a local PKE predicate stays true when the trace grows is a `PkePred.Later`
  (the `pred_later` field of DY*'s `pke_crypto_predicate`).
  Local PKE predicates for the usage tags `tags` are `PkePred.Local tags`
  (DY*'s `list (string & pke_crypto_predicate)`), e.g.
    `def myPred: PkePred.Local ["MyTag"] := .single { pred := ... }`
    `theorem myPredProof [BytesInvariants]: PkePred.LocalProof myPred := .single fun skUsg ... => ...`
  and are combined with `#combine into PkePred, PkePredProof from ...`.
-/

module

public import DySlop.EquationalTheories.Pke
public import DySlop.Lib.Crypto.SplitPredicate
public meta import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction
open DySlop.SplitPredicate

namespace DySlop.Pke

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/--
  Port of the `pred_later` field of `pke_crypto_predicate`:
  the PKE predicate `lpred` stays true when the trace grows
  (`PkePredProof` for a PKE predicate that is not the global instance).
-/
@[expose, reducible]
public
def PkePred.Later [BytesInvariants] (lpred: PkePred): Prop :=
  [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
  ∀ skUsg pk msg tr1 tr2,
    pk.WellFormed tr1 →
    msg.WellFormed tr1 →
    tr1 ≤ tr2 →
    PkePred.pred (self := lpred) skUsg pk msg tr1 →
    PkePred.pred (self := lpred) skUsg pk msg tr2

/-- Port of `split_pke_predicate_params`. -/
@[expose, reducible]
public
def PkePred.splitParams: SplitPredicate.Params where
  keyType := "PkeKey"
  Data := Bytes × Bytes
  LocalPred := PkePred
  apply lpred := fun [BytesWellFormed] [GetUsage] [GetLabel] skUsg data tr =>
    PkePred.pred (self := lpred) skUsg data.1 data.2 tr
  dataWellFormed := fun [BytesWellFormed] tr data =>
    data.1.WellFormed tr ∧ data.2.WellFormed tr
  LocalPredLater := fun [BytesInvariants] lpred =>
    lpred.Later
  apply_later := fun [BytesInvariants] _ h [BytesWellFormedLater] [GetUsageLater] [GetLabelLater] skUsg data tr1 tr2 h_wf h_le h_pred =>
    h skUsg data.1 data.2 tr1 tr2 h_wf.1 h_wf.2 h_le h_pred

/-- Local PKE predicates for the usage tags `tags`. -/
public
abbrev PkePred.Local (tags: List String) := PkePred.splitParams.Local tags

/-- The PKE predicate defined by local PKE predicates. -/
@[expose]
public
def PkePred.Local.pred {tags: List String} (l: PkePred.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (pk msg: Bytes) (tr: ProofTrace)
  : Prop
:=
  SplitPredicate.Params.Local.pred l skUsg (pk, msg) tr

public
theorem PkePred.Local.pred_single
  {tag: String} (lpred: PkePred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (pk msg: Bytes) (tr: ProofTrace)
  : skUsg.type = "PkeKey" →
    skUsg.tag = tag →
    PkePred.Local.pred (Locals.single (tag := tag) lpred) skUsg pk msg tr = PkePred.pred (self := lpred) skUsg pk msg tr
:=
  SplitPredicate.Params.Local.pred_single PkePred.splitParams (tag := tag) lpred skUsg (pk, msg) tr

/-- Port of `has_pke_predicate`. -/
public
class PkePred.Has [PkePred] {tags: List String} (l: PkePred.Local tags): Prop where
  pred_eq:
    ∀ [BytesWellFormed] [GetUsage] [GetLabel] (skUsg: Usage) (pk msg: Bytes) (tr: ProofTrace),
      skUsg.type = "PkeKey" →
      skUsg.tag ∈ tags →
      PkePred.pred skUsg pk msg tr = l.pred skUsg pk msg tr

public
instance PkePred.Has.ofHasStep
  [PkePred] {tags1 tags2: List String} (l1: PkePred.Local tags1) (l2: PkePred.Local tags2)
  [HasStep l1 l2] [h: PkePred.Has l2]
  : PkePred.Has l1
where
  pred_eq skUsg pk msg tr h_type h_tag := by
    rw [h.pred_eq skUsg pk msg tr h_type (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitPredicate.Params.Local.pred_of_hasStep _ l1 l2 skUsg (pk, msg) tr h_type h_tag

/-- Port of `mk_pke_predicate`. -/
@[expose, instance_reducible]
public
def PkePred.ofLocal {tags: List String} (l: PkePred.Local tags): PkePred where
  pred := l.pred

/-- Port of `mk_pke_predicate_correct`. -/
public
theorem PkePred.ofLocal_has {tags: List String} (l: PkePred.Local tags):
  letI := PkePred.ofLocal l
  PkePred.Has l
:= by
  letI := PkePred.ofLocal l
  exact ⟨fun _ _ _ _ _ _ => rfl⟩

/-- Local PKE predicates stay true when the trace grows. -/
public
abbrev PkePred.LocalProof [BytesInvariants] {tags: List String} (l: PkePred.Local tags): Prop :=
  SplitPredicate.Params.Local.Later l

public
theorem PkePred.LocalProof.single
  [BytesInvariants] {tag: String} {lpred: PkePred}
  : lpred.Later →
    PkePred.LocalProof (Locals.single (tag := tag) lpred)
:=
  Locals.All.single (prop := fun _ lpred => PkePred.splitParams.LocalPredLater lpred)

public
theorem PkePred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (tags: List String) × PkePred.Local tags)
  : (∀ id, PkePred.LocalProof (ls id).2) →
    PkePred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

/-- Port of the `pred_later` field of `mk_pke_predicate`. -/
public
theorem PkePred.LocalProof.toGlobal
  [BytesInvariants] {tags: List String} {l: PkePred.Local tags}
  : PkePred.LocalProof l →
    letI := PkePred.ofLocal l
    PkePredProof
:= by
  intro h
  letI := PkePred.ofLocal l
  exact ⟨fun skUsg pk msg tr1 tr2 h_pk h_msg h_le =>
    SplitPredicate.Params.Local.Later.pred_later _ l h skUsg (pk, msg) tr1 tr2 ⟨h_pk, h_msg⟩ h_le⟩

end DySlop.Pke

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* PkePred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `pkePred
      localTypeName := ``DySlop.Pke.PkePred.Local
      mkTopLevel := DySlop.SplitFunction.Combine.globalInstances
        ``DySlop.Pke.PkePred ``DySlop.Pke.PkePred.ofLocal ``DySlop.Pke.PkePred.Has ``DySlop.Pke.PkePred.ofLocal_has
    }

macro_rules
  | `(command| #combine_one $options* PkePredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `pkePredProof
      refereeName := `pkePred
      localProofName := ``DySlop.Pke.PkePred.LocalProof
      combineName := ``DySlop.Pke.PkePred.LocalProof.combine
      mkTopLevel := DySlop.SplitFunction.Combine.globalProofInstance
        ``DySlop.Pke.PkePredProof ``DySlop.Pke.PkePred.LocalProof.toGlobal
    }

end DY.Meta.CombineMacro
