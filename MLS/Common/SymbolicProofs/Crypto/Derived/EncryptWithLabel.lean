module

public import MLS.Common.SymbolicProofs.Crypto.Derived.MlsLabel
public import MLS.Symbolic.Code.Symbolic
public import DySlop.Lib.HPKE

/-!
Port of `MLS.Crypto.Derived.Symbolic.EncryptWithLabel`: split HPKE predicate for EncryptWithLabel,
and lemmas on `encryptWithLabel` and `decryptWithLabel`.

Local EncryptWithLabel predicates for the labels `labels` are `EncryptWithLabelPred.Local labels`, e.g.
  `def myPred: EncryptWithLabelPred.Local ["UpdatePathNode"] := .single { pred := ... }`
and are combined with `#combine into EncryptWithLabelPred, EncryptWithLabelPredProof from ...`.
As for ExpandWithLabel, the HPKE usage tag of the key (e.g. `"MLS.NodeHpkeKey"`) is a parameter:
the local HPKE predicate defined by local EncryptWithLabel predicates `l` is `EncryptWithLabelPred.toHpkePred tag l`,
to be combined into `HpkePred`, and `EncryptWithLabelPred.Has.ofToHpkePred` derives `EncryptWithLabelPred.Has tag l`.

Port-specific differences:
- The tags are the labels without the prefix `"MLS 1.0 "` (see `parseWithMlsLabel`).
- MLS*'s `has_mls_encryptwithlabel_pred` contains `has_hpke_invariants`;
  here, the theorems take HPKE's instances `KdfExpandUsage.Has HPKE.kdfExpandUsage` and `AeadPred.Has HPKE.aeadPred`.
-/

namespace MLS

open DY
open DySlop DySlop.HPKE DySlop.SplitFunction
open Comparse

section Local

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `encryptwithlabel_crypto_pred` (without `pred_later`, see `EncryptWithLabelPred.Later`). -/
public
structure EncryptWithLabelPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → (keyUsgData msg context: Bytes) → ProofTrace → Prop

/-- Port of the `pred_later` field of `encryptwithlabel_crypto_pred`. -/
@[expose, reducible]
public
def EncryptWithLabelPred.Later [BytesInvariants] (lpred: EncryptWithLabelPred): Prop :=
  [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
  ∀ keyUsgData msg context tr1 tr2,
    msg.WellFormed tr1 →
    context.WellFormed tr1 →
    tr1 ≤ tr2 →
    lpred.pred keyUsgData msg context tr1 →
    lpred.pred keyUsgData msg context tr2

/-- Local EncryptWithLabel predicates for the labels `labels` (MLS*'s `list (valid_label & encryptwithlabel_crypto_pred)`). -/
public
abbrev EncryptWithLabelPred.Local (labels: List String) := Locals (fun _: String => EncryptWithLabelPred) labels

/-- Local EncryptWithLabel predicates stay true when the trace grows. -/
public
abbrev EncryptWithLabelPred.LocalProof [BytesInvariants] {labels: List String} (l: EncryptWithLabelPred.Local labels): Prop :=
  l.All (fun _ lpred => lpred.Later)

public
theorem EncryptWithLabelPred.LocalProof.single
  [BytesInvariants] {label: String} {lpred: EncryptWithLabelPred}
  : lpred.Later →
    EncryptWithLabelPred.LocalProof (Locals.single (tag := label) lpred)
:=
  Locals.All.single (prop := fun _ lpred => EncryptWithLabelPred.Later lpred)

public
theorem EncryptWithLabelPred.LocalProof.combine
  [BytesInvariants] {n: Nat} (ls: Fin n → (labels: List String) × EncryptWithLabelPred.Local labels)
  : (∀ id, EncryptWithLabelPred.LocalProof (ls id).2) →
    EncryptWithLabelPred.LocalProof (Locals.combine ls)
:=
  Locals.All.combine

end Local

section Code

variable [HasSymbolicBytes]

theorem computeEncryptionContext_eq_success
  (label: String) (context res: Bytes)
  : computeEncryptionContext label context = .success res →
    ∃ encryptContext: EncryptContext Bytes,
      encryptContext.label.val.val = "MLS 1.0 " ++ label ∧
      encryptContext.context.val = context ∧
      res = serializeNE EncryptContext.mf encryptContext
:= by
  simp only [computeEncryptionContext, Result.bind_eq_success, mkMlsBytes_eq_success, getMlsLabel_eq_success,
    Result.pure_eq_success]
  rintro ⟨mlsContext, rfl, mlsLabel, h_label, rfl⟩
  refine ⟨{ label := mlsLabel, context := mlsContext }, ?_⟩
  grind

public
theorem encryptWithLabel_eq_success
  (pkR: Bytes) (label: String) (context plaintext entropy: Bytes) (res: Bytes × Bytes)
  : encryptWithLabel pkR label context plaintext entropy = .success res →
    ∃ encryptContext: EncryptContext Bytes,
      encryptContext.label.val.val = "MLS 1.0 " ++ label ∧
      encryptContext.context.val = context ∧
      res = hpkeEnc pkR entropy plaintext (serializeNE EncryptContext.mf encryptContext) BytesLike.empty
:= by
  simp only [encryptWithLabel, Result.bind_eq_success, cryptoBytesBytes_hpkeEncrypt, Result.success.injEq]
  rintro ⟨contextBytes, h_context, rfl⟩
  obtain ⟨encryptContext, h_label, h_ctx, rfl⟩ := computeEncryptionContext_eq_success label context _ h_context
  refine ⟨encryptContext, ?_⟩
  grind

public
theorem decryptWithLabel_eq_success
  (skR: Bytes) (label: String) (context enc ciphertext: Bytes) (plaintext: Bytes)
  : decryptWithLabel skR label context enc ciphertext = .success plaintext →
    ∃ encryptContext: EncryptContext Bytes,
      encryptContext.label.val.val = "MLS 1.0 " ++ label ∧
      encryptContext.context.val = context ∧
      hpkeDec skR (enc, ciphertext) (serializeNE EncryptContext.mf encryptContext) BytesLike.empty = some plaintext
:= by
  simp only [decryptWithLabel, Result.bind_eq_success, cryptoBytesBytes_hpkeDecrypt]
  rintro ⟨contextBytes, h_context, h_dec⟩
  obtain ⟨encryptContext, h_label, h_ctx, rfl⟩ := computeEncryptionContext_eq_success label context _ h_context
  refine ⟨encryptContext, h_label, h_ctx, ?_⟩
  split at h_dec <;> simp_all [Result.error]

end Code

section SplitPredicate

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `split_encryptwithlabel_crypto_pred_params`. -/
@[expose, reducible]
public
def EncryptWithLabelPred.splitParams: SplitFunction.Params where
  Tag := String
  -- the instances, the HPKE usage, the message, the info, the associated data, the trace
  Input := SplitPredicate.PredInstances × (String × Bytes) × Bytes × Bytes × Bytes × ProofTrace
  -- the instances, the data of the HPKE usage, the message, the context, the trace
  RawInput := SplitPredicate.PredInstances × Bytes × Bytes × Bytes × ProofTrace
  Output := Prop
  decode x :=
    match parseWithMlsLabel EncryptContext.mf EncryptContext.label x.2.2.2.1 with
    | some (label, encryptContext) => some (label, (x.1, x.2.1.2, x.2.2.1, encryptContext.context.val, x.2.2.2.2.2))
    | none => none
  LocalFun _ := EncryptWithLabelPred
  applyLocal lpred x := @EncryptWithLabelPred.pred _ _ _ lpred x.1.wf x.1.usage x.1.label x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  default _ := False

/-- MLS*'s `apply_global_fun` of `split_encryptwithlabel_crypto_pred_params`. -/
@[expose, reducible]
public
def EncryptWithLabelPred.applyGlobal (hpred: HpkePred) (x: EncryptWithLabelPred.splitParams.Input): Prop :=
  @HpkePred.pred _ _ _ hpred x.1.wf x.1.usage x.1.label x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

theorem EncryptWithLabelPred.splitParams_decode
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace) (label: String) (encryptContext: EncryptContext Bytes)
  : parseWithMlsLabel EncryptContext.mf EncryptContext.label info = some (label, encryptContext) →
    EncryptWithLabelPred.splitParams.decode (⟨⟩, usage, msg, info, ad, tr) = some (label, (⟨⟩, usage.2, msg, encryptContext.context.val, tr))
:= by
  intro h
  simp [h]

/-- The local EncryptWithLabel predicate for the label `label`. -/
public
abbrev EncryptWithLabelPred.Local.pred {labels: List String} (l: EncryptWithLabelPred.Local labels)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (label: String) (keyUsgData msg context: Bytes) (tr: ProofTrace)
  : Prop
:=
  Params.Locals.apply EncryptWithLabelPred.splitParams l label (⟨⟩, keyUsgData, msg, context, tr) False

public
theorem EncryptWithLabelPred.Local.pred_single
  {label: String} (lpred: EncryptWithLabelPred)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsgData msg context: Bytes) (tr: ProofTrace)
  : EncryptWithLabelPred.Local.pred (Locals.single (tag := label) lpred) label keyUsgData msg context tr =
    lpred.pred keyUsgData msg context tr
:=
  Params.Locals.apply_single EncryptWithLabelPred.splitParams lpred _ _

/-- Port of `mk_hpke_mls_pred` (and of `mk_global_hpke_mls_pred`): the HPKE predicate defined by local EncryptWithLabel predicates. -/
@[expose, instance_reducible]
public
def EncryptWithLabelPred.ofLocal {labels: List String} (l: EncryptWithLabelPred.Local labels): HpkePred where
  pred usage msg info ad tr := Params.Locals.toFun EncryptWithLabelPred.splitParams l (⟨⟩, usage, msg, info, ad, tr)

theorem EncryptWithLabelPred.ofLocal_pred
  {labels: List String} (l: EncryptWithLabelPred.Local labels)
  [BytesWellFormed] [GetUsage] [GetLabel]
  (usage: String × Bytes) (msg info ad: Bytes) (tr: ProofTrace)
  : HpkePred.pred (self := EncryptWithLabelPred.ofLocal l) usage msg info ad tr =
    Params.Locals.toFun EncryptWithLabelPred.splitParams l (⟨⟩, usage, msg, info, ad, tr)
:= rfl

/-- The local HPKE predicate for the usage tag `tag`, defined by local EncryptWithLabel predicates. -/
public
abbrev EncryptWithLabelPred.toHpkePred (tag: String) {labels: List String} (l: EncryptWithLabelPred.Local labels)
  : HpkePred.Local [tag]
:=
  Locals.single (EncryptWithLabelPred.ofLocal l)

/-- Port of `has_mls_encryptwithlabel_pred` (with `has_encryptwithlabel_pred`, i.e. `has_local_fun`). -/
public
class EncryptWithLabelPred.Has [hpkePred: HpkePred] (tag: String) {labels: List String} (l: EncryptWithLabelPred.Local labels): Prop where
  pf: ∃ mlsHpkePred: HpkePred,
    -- the global HPKE predicate is explicit, otherwise `mlsHpkePred` would be used as the `HpkePred` instance
    @HpkePred.Has _ _ _ hpkePred _ (Locals.single (tag := tag) mlsHpkePred) ∧
    EncryptWithLabelPred.splitParams.HasLocal (EncryptWithLabelPred.applyGlobal mlsHpkePred) l

public
instance EncryptWithLabelPred.Has.ofHasStep
  [HpkePred] (tag: String) {labels1 labels2: List String}
  (l1: EncryptWithLabelPred.Local labels1) (l2: EncryptWithLabelPred.Local labels2)
  [HasStep l1 l2] [h: EncryptWithLabelPred.Has tag l2]
  : EncryptWithLabelPred.Has tag l1
where
  pf := by
    obtain ⟨mlsHpkePred, h_hpke, h_local⟩ := h.pf
    exact ⟨mlsHpkePred, h_hpke, Params.HasLocal.of_hasStep EncryptWithLabelPred.splitParams _ l1 l2 h_local⟩

/-- Port of `mk_hpke_mls_pred_correct`. -/
public
theorem EncryptWithLabelPred.Has.ofToHpkePred
  [HpkePred] (tag: String) {labels: List String} (l: EncryptWithLabelPred.Local labels)
  [h: HpkePred.Has (EncryptWithLabelPred.toHpkePred tag l)]
  : EncryptWithLabelPred.Has tag l
:=
  ⟨⟨EncryptWithLabelPred.ofLocal l, h, Params.Locals.toFun_hasLocal EncryptWithLabelPred.splitParams l⟩⟩

/-- The global HPKE predicate on an encryption context, given the local EncryptWithLabel predicates. -/
public
theorem EncryptWithLabelPred.Has.hpkePred_eq
  [HpkePred] {labels: List String} (l: EncryptWithLabelPred.Local labels) (tag: String) [h: EncryptWithLabelPred.Has tag l]
  [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsgData msg: Bytes) (label: String) (encryptContext: EncryptContext Bytes) (ad: Bytes) (tr: ProofTrace)
  : encryptContext.label.val.val = "MLS 1.0 " ++ label →
    label ∈ labels →
    HpkePred.pred (tag, keyUsgData) msg (serializeNE EncryptContext.mf encryptContext) ad tr =
    l.pred label keyUsgData msg encryptContext.context.val tr
:= by
  intro h_label h_mem
  obtain ⟨mlsHpkePred, h_hpke, h_local⟩ := h.pf
  have h_decode := parseWithMlsLabel_serializeNE EncryptContext.mf EncryptContext.label encryptContext label h_label
  rw [h_hpke.pred_eq _ _ _ _ _ (by simp),
    HpkePred.Local.pred_single (tag := tag) mlsHpkePred (tag, keyUsgData) msg _ ad tr rfl]
  exact h_local _ label _ (EncryptWithLabelPred.splitParams_decode _ msg _ ad tr label encryptContext h_decode) h_mem

end SplitPredicate

section LaterProofs

-- Not `[HasSymbolicInvariants]`: the top level uses these lemmas to build its `BytesInvariantsProofs`.
variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
variable [BytesInvariants.Has DY.Literal.invariants] [BytesInvariants.Has DY.Concat.invariants]

/-- Port of `mk_global_hpke_mls_pred_later`. -/
public
theorem EncryptWithLabelPred.ofLocal_later
  {labels: List String} (l: EncryptWithLabelPred.Local labels)
  : EncryptWithLabelPred.LocalProof l →
    (EncryptWithLabelPred.ofLocal l).Later
:= by
  intro h _ _ _ usage msg info ad tr1 tr2 h_msg h_info _ h_le
  rw [EncryptWithLabelPred.ofLocal_pred, EncryptWithLabelPred.ofLocal_pred]
  cases h_decode: parseWithMlsLabel EncryptContext.mf EncryptContext.label info with
  | none => simp [Params.Locals.toFun_eq_default, h_decode]
  | some x =>
    obtain ⟨label, encryptContext⟩ := x
    have h_context := wf_of_parseWithMlsLabel EncryptContext.mf EncryptContext.label (Bytes.WellFormed · tr1) info label encryptContext h_decode h_info
    rw [Params.Locals.toFun_eq EncryptWithLabelPred.splitParams l _ label _ (EncryptWithLabelPred.splitParams_decode usage msg info ad tr1 label encryptContext h_decode),
      Params.Locals.toFun_eq EncryptWithLabelPred.splitParams l _ label _ (EncryptWithLabelPred.splitParams_decode usage msg info ad tr2 label encryptContext h_decode)]
    apply Params.Locals.apply_rel EncryptWithLabelPred.splitParams l label _ _ _ _ (fun p1 p2 => p1 → p2)
    · intro x h_mem
      simp only [EncryptContext.mf.wf_eq] at h_context
      apply h x h_mem <;> grind
    · exact id

/-- The local HPKE predicate for the usage tag `tag` stays true when the trace grows. -/
public
theorem EncryptWithLabelPred.LocalProof.toHpkePred
  (tag: String) {labels: List String} {l: EncryptWithLabelPred.Local labels}
  : EncryptWithLabelPred.LocalProof l →
    HpkePred.LocalProof (EncryptWithLabelPred.toHpkePred tag l)
:= fun h =>
  HpkePred.LocalProof.single (EncryptWithLabelPred.ofLocal_later l h)

end LaterProofs

section Proofs

variable [HasSymbolicInvariants]

/-- Port of `bytes_invariant_encrypt_with_label`. -/
public
theorem encryptWithLabel.Invariant
  [BytesInvariantsProofs] [KdfExpand.KdfExpandUsage.Has HPKE.kdfExpandUsage] [Aead.AeadPred.Has HPKE.aeadPred]
  {labels: List String} (l: EncryptWithLabelPred.Local labels) (tag: String) [EncryptWithLabelPred.Has tag l]
  (keyUsgData: Bytes) (tr: ProofTrace)
  (pkR: Bytes) (label: String) (context plaintext entropy: Bytes) (enc ciphertext: Bytes)
  : encryptWithLabel pkR label context plaintext entropy = .success (enc, ciphertext) →
    pkR.Invariant tr →
    entropy.Invariant tr →
    context.Invariant tr →
    plaintext.Invariant tr →
    (plaintext.label tr).canFlow (entropy.label tr) tr.erase →
    (entropy.label tr).canFlow (pkR.hpkeSkLabel tr) tr.erase →
    entropy.HasUsage (mkHpkeEntropyUsage (tag, keyUsgData)) tr →
    (
      (
        pkR.HpkeSkHasUsage (mkHpkeSkUsage (tag, keyUsgData)) tr ∧
        l.pred label keyUsgData plaintext context tr
      ) ∨ (
        (entropy.label tr).canFlow Label.pub tr.erase
      )
    ) →
    label ∈ labels →
    enc.Publishable tr ∧ ciphertext.Publishable tr
:= by
  intro h_encrypt h_pk h_entropy h_context h_plaintext h_msgFlow h_entropyFlow h_entropyUsg h_honest h_label
  obtain ⟨encryptContext, h_mlsLabel, rfl, h_res⟩ := encryptWithLabel_eq_success pkR label _ plaintext entropy _ h_encrypt
  have h_info := (pred_serializeNE_iff EncryptContext.mf (Bytes.Invariant · tr) encryptContext).2 (by simpa using h_context)
  have h_ad := BytesCompatiblePred.pred_empty (pred := (Bytes.Publishable · tr))
  have := EncryptWithLabelPred.Has.hpkePred_eq l tag keyUsgData plaintext label encryptContext BytesLike.empty tr h_mlsLabel h_label
  have := hpkeEnc.Invariant tr pkR entropy plaintext _ _ (tag, keyUsgData) h_pk h_entropy h_plaintext h_info h_ad
    h_msgFlow h_entropyFlow h_entropyUsg (by grind)
  grind

/-- Port of `bytes_invariant_decrypt_with_label`. -/
public
theorem decryptWithLabel.Invariant
  [KdfExpand.KdfExpandUsage.Has HPKE.kdfExpandUsage] [Aead.AeadPred.Has HPKE.aeadPred]
  {labels: List String} (l: EncryptWithLabelPred.Local labels) (tag: String) [EncryptWithLabelPred.Has tag l]
  (keyUsgData: Bytes) (tr: ProofTrace)
  (skR: Bytes) (label: String) (context enc ciphertext: Bytes) (plaintext: Bytes)
  : decryptWithLabel skR label context enc ciphertext = .success plaintext →
    skR.Invariant tr →
    skR.HasUsage (mkHpkeSkUsage (tag, keyUsgData)) tr →
    enc.Invariant tr →
    context.Invariant tr →
    ciphertext.Invariant tr →
    label ∈ labels →
    plaintext.KnowableBy (skR.label tr) tr ∧
    (l.pred label keyUsgData plaintext context tr ∨ plaintext.Publishable tr)
:= by
  intro h_decrypt h_sk h_skUsg h_enc h_context h_ciphertext h_label
  obtain ⟨encryptContext, h_mlsLabel, rfl, h_dec⟩ := decryptWithLabel_eq_success skR label _ enc ciphertext plaintext h_decrypt
  have h_info := (pred_serializeNE_iff EncryptContext.mf (Bytes.Invariant · tr) encryptContext).2 (by simpa using h_context)
  have h_ad := BytesCompatiblePred.pred_empty (pred := (Bytes.Invariant · tr))
  have := EncryptWithLabelPred.Has.hpkePred_eq l tag keyUsgData plaintext label encryptContext BytesLike.empty tr h_mlsLabel h_label
  have := hpkeDec.Invariant tr skR enc ciphertext _ _ (tag, keyUsgData) plaintext h_dec h_sk h_skUsg h_enc h_ciphertext h_info h_ad
  grind

end Proofs

end MLS

/-! ## Support for the `#combine` macro -/

namespace DY.Meta.CombineMacro

/-- `#combine into EncryptWithLabelPred from A, B` combines `A.encryptWithLabelPred` and `B.encryptWithLabelPred`. -/
macro_rules
  | `(command| #combine_one $options* EncryptWithLabelPred $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkCombine options.toplevel params sources.getElems {
      name := `encryptWithLabelPred
      localTypeName := ``MLS.EncryptWithLabelPred.Local
      mkTopLevel := fun _ => pure #[]
    }

/--
  `#combine into EncryptWithLabelPredProof from A, B` combines the proofs `A.encryptWithLabelPredProof`
  and `B.encryptWithLabelPredProof` into `encryptWithLabelPredProof`.
-/
macro_rules
  | `(command| #combine_one $options* EncryptWithLabelPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[← `(bracketedBinder| [DY.BytesFunctor]), ← `(bracketedBinder| [DY.ExecTraceTypes]), ← `(bracketedBinder| [DY.ProofTraceTypes]), ← `(bracketedBinder| [DY.BytesInvariants])]
    let params := if options.toplevel then params else baseParams ++ params
    return Lean.mkNullNode <| ← DySlop.SplitFunction.Combine.mkProofCombine options.toplevel params sources.getElems {
      name := `encryptWithLabelPredProof
      refereeName := `encryptWithLabelPred
      localProofName := ``MLS.EncryptWithLabelPred.LocalProof
      combineName := ``MLS.EncryptWithLabelPred.LocalProof.combine
      mkTopLevel := fun _ => pure #[]
    }

end DY.Meta.CombineMacro
