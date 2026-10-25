/-
  Port of `DY.Lib.Crypto.MAC.Split`: split MAC predicates.

  As in DY*, local MAC predicates have the type of the global one (`MacPred`, DY*'s `mac_crypto_predicate`),
  and the proof that a local MAC predicate stays true when the trace grows is a `MacPred.Later`
  (the `pred_later` field of DY*'s `mac_crypto_predicate`).
  Local MAC predicates for the usage tags `tags` are `MacPred.Local tags`
  (DY*'s `list (string & mac_crypto_predicate)`), e.g.
    `def myPred: MacPred.Local ["MyTag"] := .single { pred := ... }`
    `theorem myPredProof [BytesInvariants]: MacPred.LocalProof myPred := .single fun keyUsg ... => ...`
  and are combined with `#combine into MacPred, MacPredProof from ...`.
-/

module

public import DySlop.EquationalTheories.Mac
public import DySlop.Lib.Crypto.SplitPredicate
public meta import DySlop.Lib.Utils.SplitFunction

open DY
open DySlop.SplitFunction
open DySlop.SplitPredicate

namespace DySlop.Mac

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/--
  Port of the `pred_later` field of `mac_crypto_predicate`:
  the MAC predicate `lpred` stays true when the trace grows
  (`MacPredProof` for a MAC predicate that is not the global instance).
-/
@[expose, reducible]
public
def MacPred.Later [BytesInvariants] (lpred: MacPred): Prop :=
  [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
  ∀ keyUsg key msg tr1 tr2,
    key.WellFormed tr1 →
    msg.WellFormed tr1 →
    tr1 ≤ tr2 →
    MacPred.pred (self := lpred) keyUsg key msg tr1 →
    MacPred.pred (self := lpred) keyUsg key msg tr2

/-- Port of `split_mac_predicate_params`. -/
@[expose, reducible]
public
def MacPred.splitParams: SplitPredicate.Params where
  KeyUsage := Usage
  getTag := SplitPredicate.usageTag "MacKey"
  Data := Bytes × Bytes
  LocalPred := MacPred
  apply lpred := fun [BytesWellFormed] [GetUsage] [GetLabel] keyUsg data tr =>
    MacPred.pred (self := lpred) keyUsg data.1 data.2 tr
  dataWellFormed := fun [BytesWellFormed] tr data =>
    data.1.WellFormed tr ∧ data.2.WellFormed tr
  LocalPredLater := fun [BytesInvariants] lpred =>
    lpred.Later
  apply_later := fun [BytesInvariants] _ h [BytesWellFormedLater] [GetUsageLater] [GetLabelLater] keyUsg data tr1 tr2 h_wf h_le h_pred =>
    h keyUsg data.1 data.2 tr1 tr2 h_wf.1 h_wf.2 h_le h_pred

/-- Local MAC predicates for the usage tags `tags`. -/
public
abbrev MacPred.Local (tags: List String) := MacPred.splitParams.Local tags

/-- The MAC predicate defined by local MAC predicates. -/
@[expose]
public
def MacPred.Local.pred {tags: List String} (l: MacPred.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: Usage) (key msg: Bytes) (tr: ProofTrace)
  : Prop
:=
  SplitPredicate.Params.Local.pred l keyUsg (key, msg) tr

public
theorem MacPred.Local.pred_single
  {tag: String} (lpred: MacPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsg: Usage) (key msg: Bytes) (tr: ProofTrace)
  : keyUsg.type = "MacKey" →
    keyUsg.tag = tag →
    MacPred.Local.pred (Locals.single (tag := tag) lpred) keyUsg key msg tr = MacPred.pred (self := lpred) keyUsg key msg tr
:=
  fun h_type h_tag =>
    SplitPredicate.Params.Local.pred_single MacPred.splitParams (tag := tag) lpred keyUsg (key, msg) tr (SplitPredicate.usageTag_eq_some h_type h_tag)

/-- Port of `has_mac_predicate`. -/
public
class MacPred.Has [MacPred] {tags: List String} (l: MacPred.Local tags): Prop where
  pred_eq:
    ∀ [BytesWellFormed] [GetUsage] [GetLabel] (keyUsg: Usage) (key msg: Bytes) (tr: ProofTrace),
      keyUsg.type = "MacKey" →
      keyUsg.tag ∈ tags →
      MacPred.pred keyUsg key msg tr = l.pred keyUsg key msg tr

public
instance MacPred.Has.ofHasStep
  [MacPred] {tags1 tags2: List String} (l1: MacPred.Local tags1) (l2: MacPred.Local tags2)
  [HasStep l1 l2] [h: MacPred.Has l2]
  : MacPred.Has l1
where
  pred_eq keyUsg key msg tr h_type h_tag := by
    rw [h.pred_eq keyUsg key msg tr h_type (HasStep.mem_tags l1 l2 _ h_tag)]
    exact SplitPredicate.Params.Local.pred_of_hasStep _ l1 l2 keyUsg (key, msg) tr _ (SplitPredicate.usageTag_eq_some h_type rfl) h_tag

/-- Port of `mk_mac_predicate`. -/
@[expose, instance_reducible]
public
def MacPred.ofLocal {tags: List String} (l: MacPred.Local tags): MacPred where
  pred := l.pred

/-- Port of `mk_mac_predicate_correct`. -/
public
theorem MacPred.ofLocal_has {tags: List String} (l: MacPred.Local tags):
  letI := MacPred.ofLocal l
  MacPred.Has l
:= by
  letI := MacPred.ofLocal l
  exact ⟨fun _ _ _ _ _ _ => rfl⟩

/-- Local MAC predicates stay true when the trace grows. -/
public
abbrev MacPred.LocalProof [BytesInvariants] {tags: List String} (l: MacPred.Local tags): Prop :=
  SplitPredicate.Params.Local.Later l

public
theorem MacPred.LocalProof.single
  [BytesInvariants] {tag: String} {lpred: MacPred}
  : lpred.Later →
    MacPred.LocalProof (Locals.single (tag := tag) lpred)
:=
  Locals.All.single (prop := fun _ lpred => MacPred.splitParams.LocalPredLater lpred)

public
theorem MacPred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (tags: List String) × MacPred.Local tags)
  : (∀ id, MacPred.LocalProof (ls id).2) →
    MacPred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

/-- Port of the `pred_later` field of `mk_mac_predicate`. -/
public
theorem MacPred.LocalProof.toGlobal
  [BytesInvariants] {tags: List String} {l: MacPred.Local tags}
  : MacPred.LocalProof l →
    letI := MacPred.ofLocal l
    MacPredProof
:= by
  intro h
  letI := MacPred.ofLocal l
  exact ⟨fun keyUsg key msg tr1 tr2 h_key h_msg h_le =>
    SplitPredicate.Params.Local.Later.pred_later _ l h keyUsg (key, msg) tr1 tr2 ⟨h_key, h_msg⟩ h_le⟩

end DySlop.Mac

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* MacPred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `macPred
      localTypeName := ``DySlop.Mac.MacPred.Local
      mkTopLevel := DySlop.SplitFunction.Combine.globalInstances
        ``DySlop.Mac.MacPred ``DySlop.Mac.MacPred.ofLocal ``DySlop.Mac.MacPred.Has ``DySlop.Mac.MacPred.ofLocal_has
    }

macro_rules
  | `(command| #combine_one $options* MacPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `macPredProof
      refereeName := `macPred
      localProofName := ``DySlop.Mac.MacPred.LocalProof
      combineName := ``DySlop.Mac.MacPred.LocalProof.combine
      mkTopLevel := DySlop.SplitFunction.Combine.globalProofInstance
        ``DySlop.Mac.MacPredProof ``DySlop.Mac.MacPred.LocalProof.toGlobal
    }

end DY.Meta.CombineMacro
