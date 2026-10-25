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

namespace DySlop.HPKE

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/-- Local HPKE predicates for the usage tags `tags` (DY*'s `list (string & hpke_crypto_predicate)`). -/
public
abbrev HpkePred.Local (tags: List String) := Locals (fun _: String => HpkePred) tags

/--
  The HPKE predicate defined by local HPKE predicates
  (DY*'s `mk_global_crypto_predicate split_hpke_predicate_params`).
-/
@[expose]
public
def HpkePred.Local.pred {tags: List String} (l: HpkePred.Local tags)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace)
  : Prop
:=
  match findLocalFun l.list usage.1 with
  | some ⟨_, lpred⟩ => HpkePred.pred (self := lpred) usage msg info ad tr
  | none => False

public
theorem HpkePred.Local.pred_single
  {tag: String} (lpred: HpkePred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace)
  : usage.1 = tag →
    HpkePred.Local.pred (Locals.single (tag := tag) lpred) usage msg info ad tr =
    HpkePred.pred (self := lpred) usage msg info ad tr
:= by
  intro h
  simp [HpkePred.Local.pred, Locals.single, findLocalFun, h]

public
theorem HpkePred.Local.pred_of_hasStep
  {tags1 tags2: List String} (l1: HpkePred.Local tags1) (l2: HpkePred.Local tags2) [h: HasStep l1 l2]
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace)
  : usage.1 ∈ tags1 →
    l2.pred usage msg info ad tr = l1.pred usage msg info ad tr
:= by
  intro h_tag
  simp [HpkePred.Local.pred, h.findLocalFun_eq usage.1 h_tag]

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
    exact HpkePred.Local.pred_of_hasStep l1 l2 usage msg info ad tr h_tag

/-- Port of `mk_hpke_predicate`. -/
@[expose, instance_reducible]
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
  l.All (fun _ lpred => HpkePred.Later lpred)

public
theorem HpkePred.LocalProof.single
  [BytesInvariants] {tag: String} {lpred: HpkePred}
  : lpred.Later →
    HpkePred.LocalProof (Locals.single (tag := tag) lpred)
:=
  Locals.All.single (prop := fun _ lpred => HpkePred.Later lpred)

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
  refine ⟨fun usage msg info ad tr1 tr2 h_msg h_info h_ad h_le h_pred => ?_⟩
  change l.pred usage msg info ad tr1 at h_pred
  change l.pred usage msg info ad tr2
  unfold HpkePred.Local.pred at *
  split at h_pred
  · rename_i h_find
    have := h _ (mem_of_findLocalFun_eq_some _ _ _ h_find)
    grind
  · grind

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
