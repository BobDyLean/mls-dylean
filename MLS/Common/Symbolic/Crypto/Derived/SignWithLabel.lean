import MLS.Common.Symbolic.Crypto.Derived.MlsLabel
import MLS.Symbolic.Code.Symbolic
import DySlop.Lib.Crypto.Signature.Split

/-!
Port of `MLS.Crypto.Derived.Symbolic.SignWithLabel`: split predicate for SignWithLabel,
and lemmas on `signWithLabel` and `verifyWithLabel`.

MLS*'s `signwithlabel_crypto_pred` has the same type as `sign_crypto_predicate`:
a local SignWithLabel predicate is a `SignPred` (on the signed content), and its `pred_later` is a `SignPred.Later`.
Local SignWithLabel predicates for the labels `labels` are `SignWithLabelPred.Local labels`, e.g.
  `def myPred: SignWithLabelPred.Local ["LeafNodeTBS"] := .single { pred := ... }`
and are combined with `#combine into SignWithLabelPred, SignWithLabelPredProof from ...`.
With `+toplevel`, `#combine` defines `signWithLabelPred.signPred`, the local sign predicate for the usage tag
`"MLS.LeafSignKey"` (MLS*'s `mk_mls_sign_pred`), to be combined into `SignPred` (and similarly for proofs).

Port-specific differences: the tags are the labels without the prefix `"MLS 1.0 "` (see `parseWithMlsLabel`).
-/

namespace MLS

open DY
open DySlop DySlop.Signature DySlop.SplitFunction
open Comparse

section Local

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/-! ## Local SignWithLabel predicates -/

/-- Local SignWithLabel predicates for the labels `labels` (MLS*'s `list (valid_label & signwithlabel_crypto_pred)`). -/
abbrev SignWithLabelPred.Local (labels: List String) := Locals (fun _: String => SignPred) labels

/-- Local SignWithLabel predicates stay true when the trace grows. -/
abbrev SignWithLabelPred.LocalProof [BytesInvariants] {labels: List String} (l: SignWithLabelPred.Local labels): Prop :=
  l.All (fun _ spred => SignPred.Later spred)

theorem SignWithLabelPred.LocalProof.single
  [BytesInvariants] {label: String} {spred: SignPred}
  : spred.Later →
    SignWithLabelPred.LocalProof (Locals.single (tag := label) spred)
:=
  Locals.All.single (prop := fun _ spred => SignPred.Later spred)

theorem SignWithLabelPred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (labels: List String) × SignWithLabelPred.Local labels)
  : (∀ id, SignWithLabelPred.LocalProof (ls id).2) →
    SignWithLabelPred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

end Local

section Code

variable [HasSymbolicBytes]

theorem signWithLabel_eq_success
  (sk: Bytes) (label: String) (msg nonce signature: Bytes)
  : signWithLabel sk label msg nonce = .success signature →
    ∃ signContent: SignContent Bytes,
      signContent.label.val.val = "MLS 1.0 " ++ label ∧
      signContent.content.val = msg ∧
      signature = DySlop.Signature.sign sk nonce (serializeNE SignContent.mf signContent)
:= by
  simp only [signWithLabel, getSignContent, Result.bind_eq_success, mkMlsBytes_eq_success, getMlsLabel_eq_success,
    Result.pure_eq_success, cryptoBytesBytes_signSign, Result.success.injEq]
  rintro ⟨content, rfl, _, ⟨mlsLabel, h_label, rfl⟩, rfl⟩
  refine ⟨{ label := mlsLabel, content }, ?_⟩
  grind

theorem verifyWithLabel_eq_true
  (vk: Bytes) (label: String) (content signature: Bytes)
  : verifyWithLabel vk label content signature = true →
    ∃ signContent: SignContent Bytes,
      signContent.label.val.val = "MLS 1.0 " ++ label ∧
      signContent.content.val = content ∧
      DySlop.Signature.verify vk (serializeNE SignContent.mf signContent) signature = true
:= by
  unfold verifyWithLabel
  split
  · rename_i signContentBytes h_eq
    simp only [getSignContent, Result.bind_eq_success, mkMlsBytes_eq_success, getMlsLabel_eq_success, Result.pure_eq_success] at h_eq
    obtain ⟨mlsContent, rfl, mlsLabel, h_mlsLabel, rfl⟩ := h_eq
    intro h_verify
    refine ⟨{ label := mlsLabel, content := mlsContent }, ?_⟩
    grind [cryptoBytesBytes_signVerify]
  · simp

end Code

section SplitPredicate

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `split_signwithlabel_crypto_pred_params`. -/
@[reducible]
def SignWithLabelPred.splitParams: SplitFunction.Params where
  Tag := String
  -- the instances, the usage of the signature key, the verification key, the message, the trace
  Input := SplitPredicate.PredInstances × Usage × Bytes × Bytes × ProofTrace
  -- the instances, the usage of the signature key, the verification key, the content, the trace
  RawInput := SplitPredicate.PredInstances × Usage × Bytes × Bytes × ProofTrace
  Output := Prop
  decode x :=
    match parseWithMlsLabel SignContent.mf SignContent.label x.2.2.2.1 with
    | some (label, signContent) => some (label, (x.1, x.2.1, x.2.2.1, signContent.content.val, x.2.2.2.2))
    | none => none
  LocalFun _ := SignPred
  applyLocal spred x := @SignPred.pred _ _ _ spred x.1.wf x.1.usage x.1.label x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  default _ := False

/-- MLS*'s `apply_global_fun` of `split_signwithlabel_crypto_pred_params`. -/
@[reducible]
def SignWithLabelPred.applyGlobal (spred: SignPred) (x: SignWithLabelPred.splitParams.Input): Prop :=
  @SignPred.pred _ _ _ spred x.1.wf x.1.usage x.1.label x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem SignWithLabelPred.splitParams_decode
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (vk msg: Bytes) (tr: ProofTrace) (label: String) (signContent: SignContent Bytes)
  : parseWithMlsLabel SignContent.mf SignContent.label msg = some (label, signContent) →
    SignWithLabelPred.splitParams.decode (⟨⟩, skUsg, vk, msg, tr) = some (label, (⟨⟩, skUsg, vk, signContent.content.val, tr))
:= by
  intro h
  simp [h]

/-- The local SignWithLabel predicate for the label `label`, applied to a content. -/
abbrev SignWithLabelPred.Local.pred {labels: List String} (l: SignWithLabelPred.Local labels)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (label: String) (skUsg: Usage) (vk content: Bytes) (tr: ProofTrace)
  : Prop
:=
  Params.Locals.apply SignWithLabelPred.splitParams l label (⟨⟩, skUsg, vk, content, tr) False

theorem SignWithLabelPred.Local.pred_single
  {label: String} (spred: SignPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (vk content: Bytes) (tr: ProofTrace)
  : SignWithLabelPred.Local.pred (Locals.single (tag := label) spred) label skUsg vk content tr =
    SignPred.pred (self := spred) skUsg vk content tr
:=
  Params.Locals.apply_single SignWithLabelPred.splitParams spred _ _

/-- Port of `mk_mls_sign_pred` (and of `mk_global_mls_sign_pred`): the sign predicate defined by local SignWithLabel predicates. -/
@[instance_reducible]
def SignWithLabelPred.ofLocal {labels: List String} (l: SignWithLabelPred.Local labels): SignPred where
  pred skUsg vk msg tr := Params.Locals.toFun SignWithLabelPred.splitParams l (⟨⟩, skUsg, vk, msg, tr)

theorem SignWithLabelPred.ofLocal_pred
  {labels: List String} (l: SignWithLabelPred.Local labels)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (skUsg: Usage) (vk msg: Bytes) (tr: ProofTrace)
  : SignPred.pred (self := SignWithLabelPred.ofLocal l) skUsg vk msg tr =
    Params.Locals.toFun SignWithLabelPred.splitParams l (⟨⟩, skUsg, vk, msg, tr)
:= rfl

/-- The local sign predicate for the usage tag `"MLS.LeafSignKey"`, defined by local SignWithLabel predicates. -/
abbrev SignWithLabelPred.toSignPred {labels: List String} (l: SignWithLabelPred.Local labels): SignPred.Local ["MLS.LeafSignKey"] :=
  Locals.single (SignWithLabelPred.ofLocal l)

/-- Port of `has_mls_signwithlabel_pred` (with `has_signwithlabel_pred`, i.e. `has_local_fun`). -/
class SignWithLabelPred.Has [signPred: SignPred] {labels: List String} (l: SignWithLabelPred.Local labels): Prop where
  pf: ∃ mlsSignPred: SignPred,
    -- the global sign predicate is explicit, otherwise `mlsSignPred` would be used as the `SignPred` instance
    @SignPred.Has _ _ _ signPred _ (Locals.single (tag := "MLS.LeafSignKey") mlsSignPred) ∧
    SignWithLabelPred.splitParams.HasLocal (SignWithLabelPred.applyGlobal mlsSignPred) l

instance SignWithLabelPred.Has.ofHasStep
  [SignPred] {labels1 labels2: List String} (l1: SignWithLabelPred.Local labels1) (l2: SignWithLabelPred.Local labels2)
  [HasStep l1 l2] [h: SignWithLabelPred.Has l2]
  : SignWithLabelPred.Has l1
where
  pf := by
    obtain ⟨mlsSignPred, h_sign, h_local⟩ := h.pf
    exact ⟨mlsSignPred, h_sign, Params.HasLocal.of_hasStep SignWithLabelPred.splitParams _ l1 l2 h_local⟩

/-- Port of `mk_mls_sign_pred_correct`. -/
theorem SignWithLabelPred.Has.ofToSignPred
  [SignPred] {labels: List String} (l: SignWithLabelPred.Local labels) [h: SignPred.Has (SignWithLabelPred.toSignPred l)]
  : SignWithLabelPred.Has l
:=
  ⟨⟨SignWithLabelPred.ofLocal l, h, Params.Locals.toFun_hasLocal SignWithLabelPred.splitParams l⟩⟩

/-- The global sign predicate on a signed content, given the local SignWithLabel predicates. -/
theorem SignWithLabelPred.Has.signPred_eq
  [SignPred] {labels: List String} (l: SignWithLabelPred.Local labels) [h: SignWithLabelPred.Has l]
  [BytesWellFormed] [GetUsage] [GetLabel]
  (prin: Participant) (vk: Bytes) (label: String) (signContent: SignContent Bytes) (tr: ProofTrace)
  : signContent.label.val.val = "MLS 1.0 " ++ label →
    label ∈ labels →
    SignPred.pred (mkMlsSigkeyUsage prin) vk (serializeNE SignContent.mf signContent) tr =
    l.pred label (mkMlsSigkeyUsage prin) vk signContent.content.val tr
:= by
  intro h_label h_mem
  obtain ⟨mlsSignPred, h_sign, h_local⟩ := h.pf
  have h_decode := parseWithMlsLabel_serializeNE SignContent.mf SignContent.label signContent label h_label
  rw [h_sign.pred_eq _ _ _ _ rfl (by simp [mkMlsSigkeyUsage, Usage.sigKey]),
    SignPred.Local.pred_single (tag := "MLS.LeafSignKey") mlsSignPred (mkMlsSigkeyUsage prin) vk _ tr rfl rfl]
  exact h_local _ label _ (SignWithLabelPred.splitParams_decode _ vk _ tr label signContent h_decode) h_mem

end SplitPredicate

section Proofs

variable [HasSymbolicInvariants]

/-- Port of `mk_global_mls_sign_pred_later`. -/
theorem SignWithLabelPred.ofLocal_later
  {labels: List String} (l: SignWithLabelPred.Local labels)
  : SignWithLabelPred.LocalProof l →
    (SignWithLabelPred.ofLocal l).Later
:= by
  intro h _ _ _ skUsg vk msg tr1 tr2 h_vk h_msg h_le
  rw [SignWithLabelPred.ofLocal_pred, SignWithLabelPred.ofLocal_pred]
  cases h_decode: parseWithMlsLabel SignContent.mf SignContent.label msg with
  | none => simp [Params.Locals.toFun_eq_default, h_decode]
  | some x =>
    obtain ⟨label, signContent⟩ := x
    have h_content := wf_of_parseWithMlsLabel SignContent.mf SignContent.label (Bytes.WellFormed · tr1) msg label signContent h_decode h_msg
    rw [Params.Locals.toFun_eq SignWithLabelPred.splitParams l _ label _ (SignWithLabelPred.splitParams_decode skUsg vk msg tr1 label signContent h_decode),
      Params.Locals.toFun_eq SignWithLabelPred.splitParams l _ label _ (SignWithLabelPred.splitParams_decode skUsg vk msg tr2 label signContent h_decode)]
    apply Params.Locals.apply_rel SignWithLabelPred.splitParams l label _ _ _ _ (fun p1 p2 => p1 → p2)
    · intro x h_mem
      simp only [SignContent.mf.wf_eq] at h_content
      apply h x h_mem <;> grind
    · exact id

/-- The local sign predicate for `"MLS.LeafSignKey"` stays true when the trace grows. -/
theorem SignWithLabelPred.LocalProof.toSignPred
  {labels: List String} {l: SignWithLabelPred.Local labels}
  : SignWithLabelPred.LocalProof l →
    SignPred.LocalProof (SignWithLabelPred.toSignPred l)
:= fun h =>
  SignPred.LocalProof.single (SignWithLabelPred.ofLocal_later l h)

/-- Port of `bytes_invariant_sign_with_label`. -/
theorem signWithLabel.Invariant
  {labels: List String} (l: SignWithLabelPred.Local labels) [SignWithLabelPred.Has l]
  (tr: ProofTrace) (prin: Participant)
  (sk: Bytes) (label: String) (msg nonce signature: Bytes)
  : signWithLabel sk label msg nonce = .success signature →
    sk.Invariant tr →
    nonce.Invariant tr →
    msg.Invariant tr →
    sk.HasUsage (mkMlsSigkeyUsage prin) tr →
    nonce.HasUsage Usage.sigNonce tr →
    (sk.label tr).canFlow (nonce.label tr) tr.erase →
    label ∈ labels →
    (
      l.pred label (mkMlsSigkeyUsage prin) (DySlop.Signature.vk sk) msg tr ∨
      (sk.label tr).canFlow Label.pub tr.erase
    ) →
    signature.Invariant tr ∧
    (signature.label tr).canFlow (msg.label tr) tr.erase
:= by
  intro h_sign h_sk h_nonce h_msg h_skUsg h_nonceUsg h_flow h_label h_pred
  obtain ⟨signContent, h_mlsLabel, rfl, rfl⟩ := signWithLabel_eq_success sk label _ nonce signature h_sign
  have h_inv := (pred_serializeNE_iff SignContent.mf (Bytes.Invariant · tr) signContent).2 (by simpa using h_msg)
  have h_knowable := (pred_serializeNE_iff SignContent.mf (Bytes.KnowableBy (signContent.content.val.label tr) · tr) signContent).2
    (by simpa using ⟨h_msg, canFlowRefl _ _⟩)
  have h_eq := SignWithLabelPred.Has.signPred_eq l prin (DySlop.Signature.vk sk) label signContent tr h_mlsLabel h_label
  constructor
  · apply DySlop.Signature.sign.Invariant sk nonce _ (mkMlsSigkeyUsage prin) tr h_sk h_nonce h_inv h_skUsg h_nonceUsg h_flow
    rw [h_eq]
    grind [mkMlsSigkeyUsage, Usage.sigKey]
  · rw [DySlop.Signature.sign.label]
    exact h_knowable.2

/-- Port of `bytes_invariant_verify_with_label`. -/
theorem verifyWithLabel.Invariant
  {labels: List String} (l: SignWithLabelPred.Local labels) [SignWithLabelPred.Has l]
  (tr: ProofTrace) (prin: Participant)
  (vk: Bytes) (label: String) (content signature: Bytes)
  : vk.Invariant tr →
    content.Invariant tr →
    signature.Invariant tr →
    vk.SignkeyHasUsage (mkMlsSigkeyUsage prin) tr →
    verifyWithLabel vk label content signature = true →
    label ∈ labels →
    l.pred label (mkMlsSigkeyUsage prin) vk content tr ∨
    (vk.signkeyLabel tr).canFlow Label.pub tr.erase
:= by
  intro h_vk h_content h_signature h_usg h_verify h_label
  obtain ⟨signContent, h_mlsLabel, rfl, h_sigVerify⟩ := verifyWithLabel_eq_true vk label _ signature h_verify
  have h_inv := (pred_serializeNE_iff SignContent.mf (Bytes.Invariant · tr) signContent).2 (by simpa using h_content)
  have h_eq := SignWithLabelPred.Has.signPred_eq l prin vk label signContent tr h_mlsLabel h_label
  have := DySlop.Signature.verify.Invariant vk _ signature (mkMlsSigkeyUsage prin) tr h_vk h_inv h_signature h_usg h_sigVerify
  rw [h_eq] at this
  grind [mkMlsSigkeyUsage, Usage.sigKey]

end Proofs

end MLS

/-! ## Support for the `#combine` macro -/

namespace DY.Meta.CombineMacro

/--
  `#combine +toplevel into SignWithLabelPred from A, B` combines `A.signWithLabelPred` and `B.signWithLabelPred`
  into `signWithLabelPred`, and defines `signWithLabelPred.signPred`, the local sign predicate for `"MLS.LeafSignKey"`
  (to be combined into `SignPred`), with the instance deriving `SignWithLabelPred.Has signWithLabelPred` from it.
-/
macro_rules
  | `(command| #combine_one $options* SignWithLabelPred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `signWithLabelPred
      localTypeName := ``MLS.SignWithLabelPred.Local
      mkTopLevel := fun nameStx => do
        let signPredStx: Lean.Ident := Lean.mkIdent `signWithLabelPred.signPred
        return #[
          ← `(command|
            public def $signPredStx : DySlop.Signature.SignPred.Local ["MLS.LeafSignKey"] :=
              MLS.SignWithLabelPred.toSignPred $nameStx
          ),
          ← `(command|
            public instance [DySlop.Signature.SignPred] [h: DySlop.Signature.SignPred.Has $signPredStx]:
              MLS.SignWithLabelPred.Has $nameStx
            :=
              MLS.SignWithLabelPred.Has.ofToSignPred $nameStx (h := h)
          )
        ]
    }

/--
  `#combine +toplevel into SignWithLabelPredProof from A, B` combines the proofs `A.signWithLabelPredProof`
  and `B.signWithLabelPredProof` into `signWithLabelPredProof`,
  and proves `signWithLabelPred.signPredProof` (to be combined into `SignPredProof`).
-/
macro_rules
  | `(command| #combine_one $options* SignWithLabelPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `signWithLabelPredProof
      refereeName := `signWithLabelPred
      localProofName := ``MLS.SignWithLabelPred.LocalProof
      combineName := ``MLS.SignWithLabelPred.LocalProof.combine
      mkTopLevel := fun nameStx => do
        let signPredProofStx: Lean.Ident := Lean.mkIdent `signWithLabelPred.signPredProof
        let signPredStx: Lean.Ident := Lean.mkIdent `signWithLabelPred.signPred
        return #[
          ← `(command|
            public theorem $signPredProofStx : DySlop.Signature.SignPred.LocalProof $signPredStx :=
              MLS.SignWithLabelPred.LocalProof.toSignPred $nameStx
          )
        ]
    }

end DY.Meta.CombineMacro
