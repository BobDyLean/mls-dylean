module

public import MLS.Bootstrap.SymbolicSpec.KeyPackage
public import MLS.Bootstrap.SymbolicProofs.State.InitKey
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.TreeSync.SymbolicProofs.LeafNodeSignature
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import MLS.Common.SymbolicProofs.Crypto.Derived.SignWithLabel
public import DySlop.Lib.Label
public import DySlop.Lib.Event
import all MLS.Bootstrap.SymbolicSpec.KeyPackage

/-!
Port of the predicates and lemmas of `MLS.Bootstrap.Symbolic.KeyPackage`:
the signature predicate of key packages, the event predicate of their verification,
and the labels of the init keys of key packages.

Port-specific differences:
- DY*'s `event_triggered_label prin {key_package}` is DyLean's `ProtocolEvent.label` of the event
  (whose principal is the field `prin`).
- The events of the lemmas are on the erased trace (`tr.erase`), as in DyLean's examples.
- MLS*'s `has_key_package_invariant` is the class `HasKeyPackageInvariant`,
  whose fields are scoped instances in `MLS.Bootstrap`.
- MLS* uses `Some?.v (key_package_to_principal key_package)`:
  the lemmas conclude with the existence of the principal (`keyPackageToPrincipal kp = some prin`).
- The signature predicate needs the well-formedness of the init key to stay true when the trace grows:
  its proof `keyPackageSignPredProof` assumes the invariants of KEM public keys (`DySlop.Kem.KemPub.invariants`).
-/

namespace MLS.Bootstrap

open Comparse
open DY
open DySlop DySlop.HPKE DySlop.Signature
open MLS MLS.TreeSync

/-! ## KeyPackage signature -/

section SignPredicate

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]

/-- The pred field of `key_package_sign_pred`. -/
@[expose]
public
def KeyPackageTbsPred [BytesWellFormed] [GetUsage] [GetLabel] (skUsg: Usage) (kpTbsBytes: Bytes) (tr: ProofTrace): Prop :=
  match (KeyPackageTBS.mf TreeKEM.tkt).toExtensible.parse kpTbsBytes with
  | none => False
  | some kpTbs =>
    ∃ prin,
      skUsg = mkMlsSigkeyUsage prin ∧
      kpTbs.initKey.val.WellFormed tr ∧
      kpTbs.initKey.val.hpkeSkLabel tr = initKeyLabel prin kpTbs.initKey.val ∧
      kpTbs.initKey.val.HpkeSkHasUsage (initKeyUsage prin kpTbs.leafNode.data.content.val) tr

/-- Port of `key_package_sign_pred` (with `key_package_tbs_tag_and_invariant`). -/
@[expose]
public
def keyPackageSignPred: SignWithLabelPred.Local ["KeyPackageTBS"] :=
  .single { pred skUsg _vk kpTbsBytes tr := KeyPackageTbsPred skUsg kpTbsBytes tr }

/-- Port of the `pred_later` field of `key_package_sign_pred`. -/
public
theorem keyPackageSignPredProof [BytesInvariants] [BytesInvariants.Has DySlop.Kem.KemPub.invariants]:
  SignWithLabelPred.LocalProof keyPackageSignPred
:=
  .single fun skUsg _vk kpTbsBytes tr1 tr2 _ hmsg hle h => by
    change KeyPackageTbsPred skUsg kpTbsBytes tr1 at h
    change KeyPackageTbsPred skUsg kpTbsBytes tr2
    unfold KeyPackageTbsPred at *
    split at h <;> grind [Bytes.kemSkLabel_later, Bytes.KemSkHasUsage_later]

/-- The key package signature predicate of `prin`, on a serialized `KeyPackageTBS`. -/
theorem keyPackageTbsPred_serializeNE [BytesWellFormed] [GetUsage] [GetLabel]
  (prin: Participant) (kpTbs: KeyPackageTBS Bytes TreeKEM.tkt) (tr: ProofTrace):
  KeyPackageTbsPred (mkMlsSigkeyUsage prin) (serializeNE (KeyPackageTBS.mf TreeKEM.tkt) kpTbs) tr ↔
    kpTbs.initKey.val.WellFormed tr ∧
    kpTbs.initKey.val.hpkeSkLabel tr = initKeyLabel prin kpTbs.initKey.val ∧
    kpTbs.initKey.val.HpkeSkHasUsage (initKeyUsage prin kpTbs.leafNode.data.content.val) tr
:= by
  simp [KeyPackageTbsPred, mkMlsSigkeyUsage_injective.eq_iff]

end SignPredicate

/-! ## KeyPackage signature verification event -/

section EventPredicate

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `key_package_has_been_verified_pred`. -/
@[expose]
public
def keyPackageHasBeenVerifiedPred (tr: ProofTrace) (ev: KeyPackageHasBeenVerified): Prop :=
  ev.keyPackage.tbs.leafNode.data.source = .keyPackage ∧
  -- preconditions of `verifyWithLabel.Invariant`
  (KeyPackage.mf TreeKEM.tkt).wf (Bytes.Invariant · tr) ev.keyPackage ∧
  (∃ token, (dyAsp tr).credentialOk (leafNodeToAsInput ev.keyPackage.tbs.leafNode) token) ∧
  -- verification succeeded
  verifyWithLabel ev.keyPackage.tbs.leafNode.data.signatureKey.val keyPackageLabel
    (serializeNE (KeyPackageTBS.mf TreeKEM.tkt) ev.keyPackage.tbs) ev.keyPackage.signature.val = true

variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]

/--
Port of `has_key_package_invariant` (with `has_key_package_tbs_invariant` and `has_key_package_has_been_verified_invariant`):
the signature predicate of key packages and the event predicate of their verification are in the protocol invariants.
The fields are scoped instances in the namespace `MLS.Bootstrap`; the top-level protocol provides them
(`instance: HasKeyPackageInvariant where`).
-/
public
class HasKeyPackageInvariant [TraceInvariant] where
  [keyPackageTbs: SignWithLabelPred.Has keyPackageSignPred]
  [proofTrace0: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT KeyPackageHasBeenVerified)]
  [eventInv0: ProtocolEvent.EventInv KeyPackageHasBeenVerified]
  [traceInv0: TraceInvariant.Has (ProtocolEvent.ProofEntryT KeyPackageHasBeenVerified)]
  [eventPred0: ProtocolEvent.EventInv.Has keyPackageHasBeenVerifiedPred]

attribute [scoped instance] HasKeyPackageInvariant.keyPackageTbs
attribute [reducible, scoped instance] HasKeyPackageInvariant.proofTrace0
attribute [scoped instance] HasKeyPackageInvariant.traceInv0
attribute [reducible, scoped instance] HasKeyPackageInvariant.eventInv0
attribute [scoped instance] HasKeyPackageInvariant.eventPred0

end EventPredicate

section Verified

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]

/-- Port of `i_have_verified_every_key_package_later`. -/
public
theorem IHaveVerifiedEveryKeyPackage_le (tr1 tr2: ExecTrace) (me: Participant)
  (joiners: List (KeyPackage Bytes TreeKEM.tkt))
  : tr1 ≤ tr2 →
    IHaveVerifiedEveryKeyPackage tr1 me joiners →
    IHaveVerifiedEveryKeyPackage tr2 me joiners
:= by
  grind [IHaveVerifiedEveryKeyPackage, IHaveVerifiedKeyPackage]

grind_pattern IHaveVerifiedEveryKeyPackage_le => tr1 ≤ tr2, IHaveVerifiedEveryKeyPackage tr1 me joiners
grind_pattern [grind_later] IHaveVerifiedEveryKeyPackage_le => tr1 ≤ tr2, IHaveVerifiedEveryKeyPackage tr1 me joiners

end Verified

/-! ## KeyPackage label -/

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]

/-- Port of `principal_key_package_has_been_verified_label`. -/
@[expose]
public
def principalKeyPackageHasBeenVerifiedLabel (keyPackage: KeyPackage Bytes TreeKEM.tkt) (prin: Participant): Label :=
  ProtocolEvent.label ({ prin, keyPackage }: KeyPackageHasBeenVerified)

/-- Port of `key_package_has_been_verified_label`. -/
@[expose]
public
def keyPackageHasBeenVerifiedLabel (keyPackage: KeyPackage Bytes TreeKEM.tkt): Label :=
  Label.bigJoin (principalKeyPackageHasBeenVerifiedLabel keyPackage)

/-- Port of `key_package_to_principal`. -/
@[expose]
public
def keyPackageToPrincipal (kp: KeyPackage Bytes TreeKEM.tkt): Option Participant :=
  credentialToPrincipal kp.tbs.leafNode.data.credential

/-- Port of `key_package_to_init_label`. -/
@[expose]
public
def keyPackageToInitLabel (kp: KeyPackage Bytes TreeKEM.tkt): Label :=
  match keyPackageToPrincipal kp with
  | none => Label.pub
  | some prin =>
    (Label.guarded (signatureKeyLabel prin kp.tbs.leafNode.data.signatureKey.val) (keyPackageHasBeenVerifiedLabel kp)).join
      (initKeyLabel prin kp.tbs.initKey.val)

omit [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)] in
/-- The label of the verification of a key package is corrupt when some principal has verified it. -/
theorem keyPackageHasBeenVerifiedLabel_isCorrupt (keyPackage: KeyPackage Bytes TreeKEM.tkt) (tr: ExecTrace):
  (keyPackageHasBeenVerifiedLabel keyPackage).isCorrupt tr ↔
    ∃ prin, tr.EventLogged ({ prin, keyPackage }: KeyPackageHasBeenVerified)
:= by
  simp [keyPackageHasBeenVerifiedLabel, principalKeyPackageHasBeenVerifiedLabel, ProtocolEvent.label_isCorrupt]

/--
Port of `key_package_to_init_label_is_corrupt`.
MLS*'s `prefix tr (find_event_triggered_at_timestamp tr me …)` is the prefix before one of the times the event was logged.
-/
public
theorem keyPackageToInitLabel_isCorrupt (tr: ExecTrace) (me prin: Participant) (keyPackage: KeyPackage Bytes TreeKEM.tkt)
  (h: (keyPackageToInitLabel keyPackage).isCorrupt tr)
  (hprin: keyPackageToPrincipal keyPackage = some prin)
  (hev: IHaveVerifiedKeyPackage tr me keyPackage):
  (∃ i, tr.EventLoggedAt ({ prin := me, keyPackage }: KeyPackageHasBeenVerified) i ∧
    (signatureKeyLabel prin keyPackage.tbs.leafNode.data.signatureKey.val).isCorrupt (tr.prefix i)) ∨
  (initKeyLabel prin keyPackage.tbs.initKey.val).isCorrupt tr
:= by
  simp only [keyPackageToInitLabel, hprin, Label.joinIsCorrupt] at h
  refine h.imp_left fun h => ?_
  apply Label.isCorrupt_guarded_event _ _ _ _ hev
  apply Label.guarded_canFlow _ _ _ _ _ _ (fun _ => canFlowRefl _ _) _ (Trace.le_refl tr) h
  exact fun _ => Label.bigJoin_canFlow _ me _

end Labels

/-! ## Init key associated to leaf node -/

section InitKeyAssociatedWith

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]

/-- Port of `key_package_has_leaf_node`. -/
@[expose]
public
def KeyPackageHasLeafNode (kp: KeyPackage Bytes TreeKEM.tkt) (ln: LeafNode Bytes TreeKEM.tkt): Prop :=
  kp.tbs.leafNode = ln

/-- Port of `init_key_associated_with_aux`. -/
@[expose]
public
def initKeyAssociatedWithAux (ln: LeafNode Bytes TreeKEM.tkt) (kp: KeyPackage Bytes TreeKEM.tkt): Label :=
  ((Label.ofProp (KeyPackageHasLeafNode kp ln)).meet (keyPackageHasBeenVerifiedLabel kp)).meet (keyPackageToInitLabel kp)

/-- Port of `init_key_associated_with`. -/
@[expose]
public
def initKeyAssociatedWith (ln: LeafNode Bytes TreeKEM.tkt): Label :=
  Label.bigJoin (initKeyAssociatedWithAux ln)

/-- Port of `init_key_associated_with_is_corrupt`. -/
public
theorem initKeyAssociatedWith_isCorrupt (tr: ExecTrace) (leafNode: LeafNode Bytes TreeKEM.tkt)
  (h: (initKeyAssociatedWith leafNode).isCorrupt tr):
  ∃ (keyPackage: KeyPackage Bytes TreeKEM.tkt) (prin: Participant),
    IHaveVerifiedKeyPackage tr prin keyPackage ∧
    keyPackage.tbs.leafNode = leafNode ∧
    (keyPackageToInitLabel keyPackage).isCorrupt tr
:= by
  obtain ⟨keyPackage, h⟩ := h
  simp only [initKeyAssociatedWithAux, Label.meetIsCorrupt, Label.ofProp_isCorrupt, KeyPackageHasLeafNode,
    keyPackageHasBeenVerifiedLabel_isCorrupt] at h
  obtain ⟨⟨hln, prin, hprin⟩, hc⟩ := h
  exact ⟨keyPackage, prin, hprin, hln, hc⟩

end InitKeyAssociatedWith

section LabelProofs

variable [HasSymbolicInvariants] [TraceInvariant]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]
variable [HasKeyPackageInvariant]

/--
Verifying the signature of a key package validated by the AS gives the key package signature predicate,
unless the signature key of its principal is corrupt.
-/
theorem keyPackageTbsPred_of_keyPackageHasBeenVerifiedPred (tr: ProofTrace) (ev: KeyPackageHasBeenVerified)
  (h: keyPackageHasBeenVerifiedPred tr ev):
  ∃ prin, keyPackageToPrincipal ev.keyPackage = some prin ∧ (
    (signatureKeyLabel prin ev.keyPackage.tbs.leafNode.data.signatureKey.val).isCorrupt tr.erase ∨
    KeyPackageTbsPred (mkMlsSigkeyUsage prin) (serializeNE (KeyPackageTBS.mf TreeKEM.tkt) ev.keyPackage.tbs) tr
  )
:= by
  obtain ⟨-, hwf, ⟨token, hcred⟩, hverif⟩ := h
  obtain ⟨prin, hcp, hvk⟩ := isSignatureKeyVk_of_credentialOk tr _ _ token hcred
  refine ⟨prin, hcp, ?_⟩
  rw [KeyPackage.mf.wf_eq] at hwf
  have htbs := (pred_serializeNE_iff (KeyPackageTBS.mf TreeKEM.tkt) (Bytes.Invariant · tr) ev.keyPackage.tbs).2 hwf.1
  have := verifyWithLabel.Invariant keyPackageSignPred tr prin _ "KeyPackageTBS" _ _
    hvk.1.1 htbs hwf.2 hvk.2.2 hverif (by simp)
  rw [canFlowPubEqIsCorrupt, ← hvk.2.1]
  exact this.symm

/--
Port of `key_package_to_init_label_lemma`.
When `me` has verified a key package, the label of its init key is at least as secret as `keyPackageToInitLabel`,
and its init key has the init key usage (unless `keyPackageToInitLabel` is corrupt).
The proof uses the guarded authentication lemma: either the signature key was corrupt before the verification,
or the key package signature predicate held before the verification.
-/
public
theorem keyPackageToInitLabel_lemma (tr: ProofTrace) (me: Participant) (keyPackage: KeyPackage Bytes TreeKEM.tkt)
  (hev: IHaveVerifiedKeyPackage tr.erase me keyPackage) (hinv: tr.Invariant):
  ∃ prin, keyPackageToPrincipal keyPackage = some prin ∧
    (keyPackageToInitLabel keyPackage).canFlow (keyPackage.tbs.initKey.val.hpkeSkLabel tr) tr.erase ∧ (
      keyPackage.tbs.initKey.val.HpkeSkHasUsage (initKeyUsage prin keyPackage.tbs.leafNode.data.content.val) tr ∨
      (keyPackageToInitLabel keyPackage).canFlow Label.pub tr.erase
    )
:= by
  obtain ⟨i, hpred⟩ := ProtocolEvent.EventInv.Has.pred_of_eventLogged keyPackageHasBeenVerifiedPred tr _ hinv hev
  obtain ⟨prin, hcp, -⟩ := keyPackageTbsPred_of_keyPackageHasBeenVerifiedPred _ _ hpred
  refine ⟨prin, hcp, ?_⟩
  have hlabel: keyPackageToInitLabel keyPackage =
      (Label.guarded (signatureKeyLabel prin keyPackage.tbs.leafNode.data.signatureKey.val)
        (keyPackageHasBeenVerifiedLabel keyPackage)).join (initKeyLabel prin keyPackage.tbs.initKey.val) := by
    simp [keyPackageToInitLabel, hcp]
  -- the label becomes corrupt when a principal `p` verifies the key package: the event predicate holds before
  have hauth: ∀ i, (keyPackageHasBeenVerifiedLabel keyPackage).isCorrupt (tr.prefix (i+1)).erase →
      ¬ (keyPackageHasBeenVerifiedLabel keyPackage).isCorrupt (tr.prefix i).erase →
      (signatureKeyLabel prin keyPackage.tbs.leafNode.data.signatureKey.val).isCorrupt (tr.prefix i).erase ∨
      KeyPackageTbsPred (mkMlsSigkeyUsage prin) (serializeNE (KeyPackageTBS.mf TreeKEM.tkt) keyPackage.tbs)
        (tr.prefix i) := by
    simp only [keyPackageHasBeenVerifiedLabel_isCorrupt, not_exists, Trace.prefix_erase]
    intro i ⟨p, hp⟩ hng
    have := ProtocolEvent.eventLoggedAt_of_prefix_succ tr.erase _ i hp (hng p)
    have := keyPackageTbsPred_of_keyPackageHasBeenVerifiedPred _ _
      (ProtocolEvent.EventInv.Has.pred_of_eventLoggedAt keyPackageHasBeenVerifiedPred tr _ i hinv this)
    grind [Trace.prefix_erase]
  have hg0: ¬ (keyPackageHasBeenVerifiedLabel keyPackage).isCorrupt (tr.prefix 0).erase := by
    simp [keyPackageHasBeenVerifiedLabel_isCorrupt, ProtocolEvent.not_eventLogged_prefix_zero]
  have hg: (keyPackageHasBeenVerifiedLabel keyPackage).isCorrupt tr.erase :=
    (keyPackageHasBeenVerifiedLabel_isCorrupt _ _).2 ⟨me, hev⟩
  rcases Label.guarded_authentication tr _ _ _ hauth hg0 hg with hg | ⟨i, -, hpred⟩
  · -- the signature key was corrupt before the verification: the label is corrupt
    grind [Label.canFlow_of_isCorrupt]
  · -- the signature predicate held before the verification
    have := Trace.prefix_le_self tr i
    grind [keyPackageTbsPred_serializeNE, Bytes.kemSkLabel_later, Bytes.KemSkHasUsage_later]

/-- Port of `init_key_associated_with_lemma`. -/
public
theorem initKeyAssociatedWith_lemma (tr: ProofTrace) (me: Participant) (keyPackage: KeyPackage Bytes TreeKEM.tkt)
  (hev: IHaveVerifiedKeyPackage tr.erase me keyPackage) (hinv: tr.Invariant):
  ∃ prin, keyPackageToPrincipal keyPackage = some prin ∧
    (initKeyAssociatedWith keyPackage.tbs.leafNode).canFlow (keyPackage.tbs.initKey.val.hpkeSkLabel tr) tr.erase ∧ (
      keyPackage.tbs.initKey.val.HpkeSkHasUsage (initKeyUsage prin keyPackage.tbs.leafNode.data.content.val) tr ∨
      (initKeyAssociatedWith keyPackage.tbs.leafNode).canFlow Label.pub tr.erase
    )
:= by
  obtain ⟨prin, hcp, hflow, hor⟩ := keyPackageToInitLabel_lemma tr me keyPackage hev hinv
  have: (initKeyAssociatedWith keyPackage.tbs.leafNode).canFlow (keyPackageToInitLabel keyPackage) tr.erase := by
    intro tr' hle hc
    refine ⟨keyPackage, ?_⟩
    simp only [initKeyAssociatedWithAux, Label.meetIsCorrupt, Label.ofProp_isCorrupt, KeyPackageHasLeafNode, true_and]
    grind [keyPackageHasBeenVerifiedLabel_isCorrupt, Trace.EventLogged_le, IHaveVerifiedKeyPackage]
  refine ⟨prin, hcp, ?_⟩
  grind [canFlowTrans]

end LabelProofs

end MLS.Bootstrap
