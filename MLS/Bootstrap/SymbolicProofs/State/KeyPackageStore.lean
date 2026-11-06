module

public import MLS.Bootstrap.SymbolicSpec.State.KeyPackageStore
public import MLS.Bootstrap.SymbolicProofs.State.InitKey
public import MLS.Bootstrap.SymbolicProofs.KeyPackageRef
public import MLS.Bootstrap.SymbolicProofs.Welcome
public import MLS.Symbolic.SymbolicProofs.Symbolic
import all MLS.Bootstrap.SymbolicSpec.State.KeyPackageStore
import DY.Meta.Step

/-!
Port of the invariant and proofs of `MLS.Bootstrap.Symbolic.State.KeyPackageStore`.

Port-specific differences:
- The state predicate (`bootstrap_key_package_store_state_pred`) is the DyLean state invariant
  `bootstrapKeyPackageStoreStateInv` (an instance, as in DyLean's examples):
  MLS*'s `has_bootstrap_key_package_store_state_invariant` is not needed.
- The proofs of the traceful functions (`initialize_key_package_store_proof`, …) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the key package store and of the init key states.
  The `tr_out == tr` part of their postconditions is not ported
  (DyLean's Hoare triples do not state that the trace is unchanged).
- `lookup_key_package_store_key_package_store_pre_to_post_proof` is split into the Hoare triple of
  `keyPackageStorePreToPost` (every converted element is good) and the pure lemma `lookupKeyPackageStore_mem`
  (the looked-up value is one of the elements).
- `for_allP p l` is `∀ x ∈ l, p x`.
-/

namespace MLS.Bootstrap

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.TreeSync

variable [HasSymbolicInvariants]

/-- Port of `key_package_store_value_to_key_package`. -/
@[expose]
public
def keyPackageStoreValueToKeyPackage (value: KeyPackageStoreValuePost): KeyPackage Bytes TreeKEM.tkt :=
  value.keyPackage

/-- Port of `key_package_store_elem_is_mine`. -/
public
def KeyPackageStoreElemIsMine (me: Participant) (x: KeyPackageStoreElemPre): Prop :=
  credentialToPrincipal x.value.keyPackage.tbs.leafNode.data.credential = some me

section StateInvariant

variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT KeyPackageStorePre)]

/--
Port of `bootstrap_key_package_store_state_pred`: the invariant of key package stores
(MLS*'s `has_bootstrap_key_package_store_state_invariant` is this instance).
-/
public
instance bootstrapKeyPackageStoreStateInv: CompromisableLocalStateInv KeyPackageStorePre where
  invariant prin st tr :=
    KeyPackageStorePre.mf.wf (Bytes.Publishable · tr) st ∧
    ∀ x ∈ st.elems, KeyPackageStoreElemIsMine prin x
  invariant_later prin st tr1 tr2 := by
    grind
  invariant_implies_KnowableBy prin st tr h := by
    simp only [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf,
      _root_.Comparse.NonExtensibleMessageFormat.toExtensible.wf_eq]
    exact wf_knowableBy_of_publishable KeyPackageStorePre.mf _ tr st h.1

end StateInvariant

section Lemmas

/-- `keyPackageStoreValueToHpkeSk` returns the init key. -/
theorem keyPackageStoreValueToHpkeSk_eq_success (value: KeyPackageStoreValuePost) (hpkeSk: Bytes)
  (h: keyPackageStoreValueToHpkeSk value = .success hpkeSk):
  hpkeSk = value.initKey
:= by
  simp only [keyPackageStoreValueToHpkeSk] at h
  split at h <;> grind [Result.error, Result.pure_eq_success]

/-- Part of `lookup_key_package_store_key_package_store_pre_to_post_proof`: the looked-up value is in the list. -/
theorem lookupKeyPackageStore_mem (l: List KeyPackageStoreElemPost) (keyPackageRef: Bytes) (v: KeyPackageStoreValuePost)
  (h: lookupKeyPackageStore l keyPackageRef = some v):
  ∃ x ∈ l, x.value = v
:= by
  induction l with
  | nil => simp [lookupKeyPackageStore] at h
  | cons hd t ih =>
    unfold lookupKeyPackageStore at h
    split at h <;> grind

end Lemmas

section Proofs

variable [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT KeyPackageStorePre)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT KeyPackageStorePre)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT KeyPackageStorePre)]

/-- Port of `initialize_key_package_store_proof`. -/
@[instance]
public
theorem initializeKeyPackageStore.proof (me: Participant):
  HoareTriple
    (initializeKeyPackageStore me)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeKeyPackageStore
  step by
    simp only [LocalStateInv.invariant, KeyPackageStorePre.mf.wf_eq]
    grind
  trivial

/-- Port of `extend_key_package_store_proof`. -/
@[instance]
public
theorem extendKeyPackageStore.proof (me: Participant) (sid: Nat) (value: KeyPackageStoreValuePre):
  HoareTriple
    (extendKeyPackageStore me sid value)
    (fun tr =>
      credentialToPrincipal value.keyPackage.tbs.leafNode.data.credential = some me ∧
      (KeyPackage.mf TreeKEM.tkt).wf (Bytes.Publishable · tr) value.keyPackage
    )
    (fun _ _ => True)
:= by
  unfold extendKeyPackageStore
  step
  step_intro
  step
  step by
    obtain ⟨-, hkp⟩ := ‹credentialToPrincipal _ = _ ∧ _›
    have := computeKeyPackageRef_knowableBy tr Label.pub value.keyPackage _ ‹_›
      (wf_knowableBy_of_publishable _ _ tr _ hkp)
    simp only [LocalStateInv.invariant] at *
    simp only [KeyPackageStorePre.mf.wf_eq, KeyPackageStoreElemPre.mf.wf_eq, KeyPackageStoreKey.mf.wf_eq,
      KeyPackageStoreValuePre.mf.wf_eq] at *
    grind [KeyPackageStoreElemIsMine, Bytes.Publishable, Bytes.KnowableBy]
  trivial

end Proofs

section Lookup

variable [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT BootstrapInitKeyState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT BootstrapInitKeyState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT BootstrapInitKeyState)]

/-- Port of `key_package_store_value_pre_to_post_proof`. -/
@[instance]
public
theorem keyPackageStoreValuePreToPost.proof (me: Participant) (valuePre: KeyPackageStoreValuePre):
  HoareTriple
    (keyPackageStoreValuePreToPost me valuePre)
    (fun _ => credentialToPrincipal valuePre.keyPackage.tbs.leafNode.data.credential = some me)
    (fun valuePost tr =>
      OneKpSecretsGood tr me keyPackageStoreValueToHpkeSk keyPackageStoreValueToKeyPackage valuePost)
:= by
  unfold keyPackageStoreValuePreToPost
  step
  step
  intro hpkeSk hsk
  obtain rfl := keyPackageStoreValueToHpkeSk_eq_success _ _ hsk
  grind [keyPackageStoreValueToKeyPackage, IsInitKeySk]

/-- Part of `lookup_key_package_store_key_package_store_pre_to_post_proof`: every converted element is good. -/
@[instance]
public
theorem keyPackageStorePreToPost.proof (me: Participant) (l: List KeyPackageStoreElemPre):
  HoareTriple
    (keyPackageStorePreToPost me l)
    (fun _ => ∀ x ∈ l, KeyPackageStoreElemIsMine me x)
    (fun lPost tr =>
      ∀ x ∈ lPost, OneKpSecretsGood tr me keyPackageStoreValueToHpkeSk keyPackageStoreValueToKeyPackage x.value)
:= by
  induction l with
  | nil =>
    unfold keyPackageStorePreToPost
    step
    grind
  | cons h t ih =>
    unfold keyPackageStorePreToPost
    step by grind [KeyPackageStoreElemIsMine, List.mem_cons_self]
    step_intro
    step
    step
    grind

section Store

variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT KeyPackageStorePre)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT KeyPackageStorePre)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT KeyPackageStorePre)]

/-- Port of `get_store_lookup_function_proof`. -/
@[instance]
public
theorem getStoreLookupFunction.proof (me: Participant) (sid: Nat):
  HoareTriple
    (getStoreLookupFunction me sid)
    (fun _ => True)
    (fun kpRefToKpSecrets tr =>
      KpSecretsGood tr me keyPackageStoreValueToHpkeSk keyPackageStoreValueToKeyPackage kpRefToKpSecrets)
:= by
  unfold getStoreLookupFunction
  step
  step by
    simp only [LocalStateInv.invariant] at *
    grind
  step
  rename_i hf
  subst hf
  intro kpRef kpSecrets hmem
  obtain ⟨elem, helem, rfl⟩ := lookupKeyPackageStore_mem _ _ _ hmem
  grind

end Store

end Lookup

end MLS.Bootstrap
