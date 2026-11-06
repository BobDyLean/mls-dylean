/-
  Port of `DY.Lib.HPKE.Split`: split HPKE predicates.

  As in DY*, local HPKE predicates have the type of the global one (`HpkePred`, DY*'s `hpke_crypto_predicate`),
  and the tag of an HPKE usage `(tag, data)` is `tag`.
  Local HPKE predicates for the usage tags `tags` are `HpkePred.Local tags`, e.g.
    `def myPred: HpkePred.Local ["MyTag"] := .single { pred := ... }`
    `theorem myPredProof [BytesInvariants]: HpkePred.LocalProof myPred := .single fun usage ... => ...`
  and are combined with `#combine into HpkePred, HpkePredProof from ...`.
-/

module

public import DySlop.Lib.HPKE.Lemmas
public meta import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction
open DySlop.SplitPredicate

namespace DySlop.HPKE

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `split_hpke_predicate_params`. -/
@[expose, reducible]
public
def HpkePred.splitParams: SplitPredicate.Params where
  KeyUsage := String × Bytes
  getTag usage := some usage.1
  -- the message, the info, the associated data
  Data := Bytes × Bytes × Bytes
  LocalPred := HpkePred
  apply lpred := fun [BytesWellFormed] [GetUsage] [GetLabel] usage data tr =>
    HpkePred.pred (self := lpred) usage data.1 data.2.1 data.2.2 tr
  dataWellFormed := fun [BytesWellFormed] tr data =>
    data.1.WellFormed tr ∧ data.2.1.WellFormed tr ∧ data.2.2.WellFormed tr
  LocalPredLater := fun [BytesInvariants] lpred =>
    lpred.Later
  apply_later := fun [BytesInvariants] _ h [BytesWellFormedLater] [GetUsageLater] [GetLabelLater] usage data tr1 tr2 h_wf h_le h_pred =>
    h usage data.1 data.2.1 data.2.2 tr1 tr2 h_wf.1 h_wf.2.1 h_wf.2.2 h_le h_pred

/-- Local HPKE predicates for the usage tags `tags` (DY*'s `list (string & hpke_crypto_predicate)`). -/
public
abbrev HpkePred.Local (tags: List String) := HpkePred.splitParams.Local tags

/-- The HPKE predicate defined by local HPKE predicates (DY*'s `mk_global_crypto_predicate split_hpke_predicate_params`). -/
public
def HpkePred.Local.pred {tags: List String} (l: HpkePred.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace)
  : Prop
:=
  SplitPredicate.Params.Local.pred l usage (msg, info, ad) tr

public
theorem HpkePred.Local.pred_single
  {tag: String} (lpred: HpkePred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace)
  : usage.1 = tag →
    HpkePred.Local.pred (Locals.single (tag := tag) lpred) usage msg info ad tr =
    HpkePred.pred (self := lpred) usage msg info ad tr
:= fun h =>
  SplitPredicate.Params.Local.pred_single HpkePred.splitParams lpred usage (msg, info, ad) tr (by simp [h])

/-- Port of `has_hpke_predicate`. -/
public
class HpkePred.Has [HpkePred] {tags: List String} (l: HpkePred.Local tags): Prop where
  pred_eq:
    ∀ [BytesWellFormed] [GetUsage] [GetLabel] (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace),
      usage.1 ∈ tags →
      HpkePred.pred usage msg info ad tr = l.pred usage msg info ad tr

public
instance HpkePred.Has.ofHasStep
  [HpkePred] {tags1 tags2: List String} (l1: HpkePred.Local tags1) (l2: HpkePred.Local tags2)
  [HasStep l1 l2] [h: HpkePred.Has l2]
  : HpkePred.Has l1
where
  pred_eq usage msg info ad tr h_tag := by
    rw [h.pred_eq usage msg info ad tr (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitPredicate.Params.Local.pred_of_hasStep _ l1 l2 usage (msg, info, ad) tr _ rfl h_tag

/-- Port of `mk_hpke_predicate`. -/
@[instance_reducible]
public
def HpkePred.ofLocal {tags: List String} (l: HpkePred.Local tags): HpkePred where
  pred := l.pred

/-- Port of `mk_hpke_predicate_correct`. -/
public
theorem HpkePred.ofLocal_has {tags: List String} (l: HpkePred.Local tags):
  letI := HpkePred.ofLocal l
  HpkePred.Has l
:= by
  letI := HpkePred.ofLocal l
  exact ⟨fun _ _ _ _ _ _ => rfl⟩

/-- Local HPKE predicates stay true when the trace grows. -/
public
abbrev HpkePred.LocalProof [BytesInvariants] {tags: List String} (l: HpkePred.Local tags): Prop :=
  SplitPredicate.Params.Local.Later l

public
theorem HpkePred.LocalProof.single
  [BytesInvariants] {tag: String} {lpred: HpkePred}
  : lpred.Later →
    HpkePred.LocalProof (Locals.single (tag := tag) lpred)
:=
  Locals.All.single (prop := fun _ lpred => HpkePred.splitParams.LocalPredLater lpred)

public
theorem HpkePred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (tags: List String) × HpkePred.Local tags)
  : (∀ id, HpkePred.LocalProof (ls id).2) →
    HpkePred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

/-- Port of the `pred_later` field of `mk_hpke_predicate`. -/
public
theorem HpkePred.LocalProof.toGlobal
  [BytesInvariants] {tags: List String} {l: HpkePred.Local tags}
  : HpkePred.LocalProof l →
    letI := HpkePred.ofLocal l
    HpkePredProof
:= by
  intro h
  letI := HpkePred.ofLocal l
  exact ⟨fun usage msg info ad tr1 tr2 h_msg h_info h_ad h_le =>
    SplitPredicate.Params.Local.Later.pred_later _ l h usage (msg, info, ad) tr1 tr2 ⟨h_msg, h_info, h_ad⟩ h_le⟩

end DySlop.HPKE

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* HpkePred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `hpkePred
      localTypeName := ``DySlop.HPKE.HpkePred.Local
      mkTopLevel := DySlop.SplitFunction.Combine.globalInstances
        ``DySlop.HPKE.HpkePred ``DySlop.HPKE.HpkePred.ofLocal ``DySlop.HPKE.HpkePred.Has ``DySlop.HPKE.HpkePred.ofLocal_has
    }

macro_rules
  | `(command| #combine_one $options* HpkePredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `hpkePredProof
      refereeName := `hpkePred
      localProofName := ``DySlop.HPKE.HpkePred.LocalProof
      combineName := ``DySlop.HPKE.HpkePred.LocalProof.combine
      mkTopLevel := DySlop.SplitFunction.Combine.globalProofInstance
        ``DySlop.HPKE.HpkePredProof ``DySlop.HPKE.HpkePred.LocalProof.toGlobal
    }

end DY.Meta.CombineMacro
