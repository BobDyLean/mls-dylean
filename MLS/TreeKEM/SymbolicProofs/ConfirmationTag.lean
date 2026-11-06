module

public import MLS.TreeKEM.Code.API.KeySchedule
public import MLS.TreeKEM.SymbolicProofs.PSK
public import MLS.Common.SymbolicProofs.Crypto.Derived.ExpandWithLabel
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeKEM.Code.KeySchedule
import all MLS.TreeKEM.Code.API.KeySchedule

/-!
Port of `MLS.TreeKEM.Symbolic.ConfirmationTag`: on symbolic bytes, the confirmation tag of a key schedule state
determines this state (and the secrets it is computed from).

Port-specific differences:
- MLS*'s `Success st == …` is `… = .success st`.
- The injectivity lemmas use the bytes invariants, as `MLS.TreeKEM.computePskSecret_inj`.
- As in MLS*, this module does not depend on the symbolic proofs of the key schedule
  (`MLS.TreeKEM.SymbolicProofs.KeySchedule` imports it, through `MLS.TreeKEM.SymbolicProofs.State.EpochSecrets`):
  the lemma on the code of the key schedule it needs (`secretJoinerToEpoch_eq_success`) is here.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open MLS MLS.TreeKEM.API.KeySchedule

/-! ## Authentication of key schedule states by their confirmation tag -/

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `compute_confirmation_tag_from_joiner_secret`. -/
public
def computeConfirmationTagFromJoinerSecret (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (groupContext: GroupContext Bytes): Result Bytes := do
  let epochSecret ← secretJoinerToEpoch joinerSecret psks groupContext
  let confirmationKey ← secretEpochToConfirmation epochSecret
  computeConfirmationTag confirmationKey groupContext.confirmedTranscriptHash.val

/-- Port of `compute_confirmation_tag_from_epoch_secret`. -/
public
def computeConfirmationTagFromEpochSecret (epochSecret: Bytes) (groupContext: GroupContext Bytes): Result Bytes := do
  let confirmationKey ← secretEpochToConfirmation epochSecret
  computeConfirmationTag confirmationKey groupContext.confirmedTranscriptHash.val

/-- Port of `treekem_keyschedule_state_auth_strong`. -/
@[expose]
public
def TreekemKeyscheduleStateAuthStrong (st: TreeKEMKeyscheduleState Bytes)
  (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes): Prop :=
  (do
    let epochSecret ← secretJoinerToEpoch joinerSecret psks groupContext
    let (newSt, _) ← createFromEpochSecret epochSecret groupContext
    pure newSt) = Result.success st

/-- Port of `treekem_keyschedule_state_auth_strong_exists`. -/
@[expose]
public
def TreekemKeyscheduleStateAuthStrongExists (st: TreeKEMKeyscheduleState Bytes): Prop :=
  ∃ joinerSecret psks groupContext, TreekemKeyscheduleStateAuthStrong st joinerSecret psks groupContext

/-- Port of `treekem_keyschedule_state_auth_weak`. -/
@[expose]
public
def TreekemKeyscheduleStateAuthWeak (st: TreeKEMKeyscheduleState Bytes)
  (epochSecret: Bytes) (groupContext: GroupContext Bytes): Prop :=
  (do
    let (newSt, _) ← createFromEpochSecret epochSecret groupContext
    pure newSt) = Result.success st

/-- Port of `treekem_keyschedule_state_auth_weak_exists`. -/
@[expose]
public
def TreekemKeyscheduleStateAuthWeakExists (st: TreeKEMKeyscheduleState Bytes): Prop :=
  ∃ epochSecret groupContext, TreekemKeyscheduleStateAuthWeak st epochSecret groupContext

/-- The confirmation tag of a key schedule state computed from an epoch secret. -/
theorem createFromEpochSecret_confirmationTag (epochSecret: Bytes) (groupContext: GroupContext Bytes)
  (st: TreeKEMKeyscheduleState Bytes) (encryptionSecret: Bytes)
  (h: createFromEpochSecret epochSecret groupContext = .success (st, encryptionSecret)):
  computeConfirmationTagFromEpochSecret epochSecret groupContext = .success st.epochKeys.confirmationTag
:= by
  simp only [createFromEpochSecret, Result.bind_eq_success, Result.pure_eq_success] at h
  simp only [computeConfirmationTagFromEpochSecret, Result.bind_eq_success]
  grind

theorem treekemKeyscheduleStateAuthWeak_iff (st: TreeKEMKeyscheduleState Bytes) (epochSecret: Bytes)
  (groupContext: GroupContext Bytes):
  TreekemKeyscheduleStateAuthWeak st epochSecret groupContext ↔
    ∃ encryptionSecret, createFromEpochSecret epochSecret groupContext = .success (st, encryptionSecret)
:= by
  simp only [TreekemKeyscheduleStateAuthWeak, Result.bind_eq_success, Result.pure_eq_success]
  grind

theorem treekemKeyscheduleStateAuthStrong_iff (st: TreeKEMKeyscheduleState Bytes) (joinerSecret: Bytes)
  (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes):
  TreekemKeyscheduleStateAuthStrong st joinerSecret psks groupContext ↔
    ∃ epochSecret, secretJoinerToEpoch joinerSecret psks groupContext = .success epochSecret ∧
      TreekemKeyscheduleStateAuthWeak st epochSecret groupContext
:= by
  simp only [TreekemKeyscheduleStateAuthStrong, TreekemKeyscheduleStateAuthWeak, Result.bind_eq_success]

/-- Port of `treekem_keyschedule_state_auth_exists_strong_to_weak`. -/
public
theorem TreekemKeyscheduleStateAuthStrongExists.weak (st: TreeKEMKeyscheduleState Bytes)
  (h: TreekemKeyscheduleStateAuthStrongExists st):
  TreekemKeyscheduleStateAuthWeakExists st
:= by
  obtain ⟨joinerSecret, psks, groupContext, h⟩ := h
  obtain ⟨epochSecret, -, h⟩ := (treekemKeyscheduleStateAuthStrong_iff _ _ _ _).1 h
  exact ⟨epochSecret, groupContext, h⟩

end CryptoBytes

/-! ## Injectivity -/

section Code

variable [HasSymbolicBytes]

public
theorem secretJoinerToEpoch_eq_success (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (groupContext: GroupContext Bytes) (epochSecret: Bytes)
  (h: secretJoinerToEpoch joinerSecret psks groupContext = .success epochSecret):
  ∃ pskSecret, computePskSecret psks = .success pskSecret ∧
    expandWithLabel (DySlop.KdfExtract.kdfExtract joinerSecret pskSecret) "epoch" (serializeNE GroupContext.mf groupContext)
      (CryptoBytes.kdfLength Bytes) = .success epochSecret
:= by
  simpa [secretJoinerToEpoch, secretJoinerToEpochInternal] using h

end Code

section Injectivity

variable [HasSymbolicInvariants]

theorem secretEpochToConfirmation_eq_success (epochSecret confirmationKey: Bytes)
  (h: secretEpochToConfirmation epochSecret = .success confirmationKey):
  ∃ kdfLabel: KdfLabel Bytes,
    confirmationKey = DySlop.KdfExpand.kdfExpand epochSecret (serializeNE KdfLabel.mf kdfLabel) (CryptoBytes.kdfLength Bytes)
:= by
  obtain ⟨kdfLabel, -, -, -, rfl⟩ := expandWithLabel_eq_success _ _ _ _ _ h
  exact ⟨kdfLabel, rfl⟩

/-- Port of `compute_confirmation_tag_from_epoch_secret_inj`. -/
public
theorem computeConfirmationTagFromEpochSecret_inj (epochSecret1: Bytes) (groupContext1: GroupContext Bytes)
  (epochSecret2: Bytes) (groupContext2: GroupContext Bytes) (confirmationTag: Bytes)
  (h1: computeConfirmationTagFromEpochSecret epochSecret1 groupContext1 = .success confirmationTag)
  (h2: computeConfirmationTagFromEpochSecret epochSecret2 groupContext2 = .success confirmationTag):
  epochSecret1 = epochSecret2
:= by
  simp only [computeConfirmationTagFromEpochSecret, computeConfirmationTag, cryptoBytesBytes_hmacHmac,
    Result.bind_eq_success, Result.success.injEq] at h1 h2
  grind [secretEpochToConfirmation_eq_success, macCompute_inj, kdfExpand_inj]

theorem computeConfirmationTagFromJoinerSecret_eq (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (groupContext: GroupContext Bytes) (epochSecret: Bytes)
  (h: secretJoinerToEpoch joinerSecret psks groupContext = .success epochSecret):
  computeConfirmationTagFromJoinerSecret joinerSecret psks groupContext =
    computeConfirmationTagFromEpochSecret epochSecret groupContext
:= by
  rw [computeConfirmationTagFromJoinerSecret, h]
  rfl

/-- Port of `compute_confirmation_tag_from_joiner_secret_inj`. -/
public
theorem computeConfirmationTagFromJoinerSecret_inj (joinerSecret1: Bytes) (psks1: List (PreSharedKeyId Bytes × Bytes))
  (groupContext1: GroupContext Bytes) (joinerSecret2: Bytes) (psks2: List (PreSharedKeyId Bytes × Bytes))
  (groupContext2: GroupContext Bytes) (confirmationTag: Bytes)
  (h1: computeConfirmationTagFromJoinerSecret joinerSecret1 psks1 groupContext1 = .success confirmationTag)
  (h2: computeConfirmationTagFromJoinerSecret joinerSecret2 psks2 groupContext2 = .success confirmationTag):
  joinerSecret1 = joinerSecret2 ∧ psks1 = psks2 ∧ groupContext1 = groupContext2
:= by
  simp only [computeConfirmationTagFromJoinerSecret, Result.bind_eq_success] at h1 h2
  obtain ⟨epochSecret1, hepoch1, h1⟩ := h1
  obtain ⟨epochSecret2, hepoch2, h2⟩ := h2
  obtain rfl := computeConfirmationTagFromEpochSecret_inj epochSecret1 groupContext1 epochSecret2 groupContext2 _
    (by simpa [computeConfirmationTagFromEpochSecret] using h1) (by simpa [computeConfirmationTagFromEpochSecret] using h2)
  obtain ⟨pskSecret1, hpsk1, hexp1⟩ := secretJoinerToEpoch_eq_success _ _ _ _ hepoch1
  obtain ⟨pskSecret2, hpsk2, hexp2⟩ := secretJoinerToEpoch_eq_success _ _ _ _ hepoch2
  have := expandWithLabel_eq_success _ _ _ _ _ hexp1
  have := expandWithLabel_eq_success _ _ _ _ _ hexp2
  grind [kdfExpand_inj, kdfExtract_inj, computePskSecret_inj]

/-- Port of `treekem_keyschedule_state_auth_weak_inj`. -/
public
theorem TreekemKeyscheduleStateAuthWeak.inj (st1: TreeKEMKeyscheduleState Bytes) (epochSecret1: Bytes)
  (groupContext1: GroupContext Bytes) (st2: TreeKEMKeyscheduleState Bytes) (epochSecret2: Bytes)
  (groupContext2: GroupContext Bytes)
  (h1: TreekemKeyscheduleStateAuthWeak st1 epochSecret1 groupContext1)
  (h2: TreekemKeyscheduleStateAuthWeak st2 epochSecret2 groupContext2)
  (htag: st1.epochKeys.confirmationTag = st2.epochKeys.confirmationTag):
  st1 = st2
:= by
  obtain ⟨enc1, h1⟩ := (treekemKeyscheduleStateAuthWeak_iff _ _ _).1 h1
  obtain ⟨enc2, h2⟩ := (treekemKeyscheduleStateAuthWeak_iff _ _ _).1 h2
  have ht1 := createFromEpochSecret_confirmationTag _ _ _ _ h1
  have ht2 := createFromEpochSecret_confirmationTag _ _ _ _ h2
  obtain rfl := computeConfirmationTagFromEpochSecret_inj _ _ _ _ _ ht1 (htag ▸ ht2)
  -- the group context is only used for the confirmation tag, which is equal
  simp only [createFromEpochSecret, Result.bind_eq_success, Result.pure_eq_success] at h1 h2
  grind

/-- Port of `treekem_keyschedule_state_auth_strong_inj`. -/
public
theorem TreekemKeyscheduleStateAuthStrong.inj (st1: TreeKEMKeyscheduleState Bytes) (joinerSecret1: Bytes)
  (psks1: List (PreSharedKeyId Bytes × Bytes)) (groupContext1: GroupContext Bytes)
  (st2: TreeKEMKeyscheduleState Bytes) (joinerSecret2: Bytes)
  (psks2: List (PreSharedKeyId Bytes × Bytes)) (groupContext2: GroupContext Bytes)
  (h1: TreekemKeyscheduleStateAuthStrong st1 joinerSecret1 psks1 groupContext1)
  (h2: TreekemKeyscheduleStateAuthStrong st2 joinerSecret2 psks2 groupContext2)
  (htag: st1.epochKeys.confirmationTag = st2.epochKeys.confirmationTag):
  st1 = st2 ∧ psks1 = psks2
:= by
  obtain ⟨epochSecret1, hepoch1, hweak1⟩ := (treekemKeyscheduleStateAuthStrong_iff _ _ _ _).1 h1
  obtain ⟨epochSecret2, hepoch2, hweak2⟩ := (treekemKeyscheduleStateAuthStrong_iff _ _ _ _).1 h2
  obtain ⟨enc1, hc1⟩ := (treekemKeyscheduleStateAuthWeak_iff _ _ _).1 hweak1
  obtain ⟨enc2, hc2⟩ := (treekemKeyscheduleStateAuthWeak_iff _ _ _).1 hweak2
  have := createFromEpochSecret_confirmationTag _ _ _ _ hc1
  have := createFromEpochSecret_confirmationTag _ _ _ _ hc2
  have := computeConfirmationTagFromJoinerSecret_eq _ _ _ _ hepoch1
  have := computeConfirmationTagFromJoinerSecret_eq _ _ _ _ hepoch2
  grind [TreekemKeyscheduleStateAuthWeak.inj, computeConfirmationTagFromJoinerSecret_inj]

/-- Port of `treekem_keyschedule_state_auth_strong_exists_inj`. -/
public
theorem TreekemKeyscheduleStateAuthStrongExists.inj (st1 st2: TreeKEMKeyscheduleState Bytes)
  (h1: TreekemKeyscheduleStateAuthStrongExists st1) (h2: TreekemKeyscheduleStateAuthStrongExists st2)
  (htag: st1.epochKeys.confirmationTag = st2.epochKeys.confirmationTag):
  st1 = st2
:= by
  obtain ⟨_, _, _, h1⟩ := h1
  obtain ⟨_, _, _, h2⟩ := h2
  exact (TreekemKeyscheduleStateAuthStrong.inj _ _ _ _ _ _ _ _ h1 h2 htag).1

/-- Port of `treekem_keyschedule_state_auth_weak_exists_inj`. -/
public
theorem TreekemKeyscheduleStateAuthWeakExists.inj (st1 st2: TreeKEMKeyscheduleState Bytes)
  (h1: TreekemKeyscheduleStateAuthWeakExists st1) (h2: TreekemKeyscheduleStateAuthWeakExists st2)
  (htag: st1.epochKeys.confirmationTag = st2.epochKeys.confirmationTag):
  st1 = st2
:= by
  obtain ⟨_, _, h1⟩ := h1
  obtain ⟨_, _, h2⟩ := h2
  exact TreekemKeyscheduleStateAuthWeak.inj _ _ _ _ _ _ h1 h2 htag

end Injectivity

end MLS.TreeKEM
