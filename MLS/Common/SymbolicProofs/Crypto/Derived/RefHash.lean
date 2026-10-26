module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Common.Proofs.Crypto.Derived

/-!
Port of `MLS.Crypto.Derived.Symbolic.RefHash`: the references computed by `refHash` are as secret as their input.
-/

namespace MLS

open Comparse
open DY

variable [HasSymbolicInvariants]

/-- Port of `ref_hash_is_knowable_by`. -/
public
theorem refHash_knowableBy (tr: ProofTrace) (l: Label) (label: String) (value: Bytes) (res: Bytes)
  (h: refHash label value = .success res) (hvalue: value.KnowableBy l tr):
  res.KnowableBy l tr
:= by
  simp only [refHash, Result.bind_eq_success, mkMlsAsciiString_eq_success, mkMlsBytes_eq_success,
    CryptoBytes.hashHash, Result.pure_eq_success] at h
  obtain ⟨label', -, value', rfl, rfl⟩ := h
  have := (pred_serializeNE_iff RefHashInput.mf (Bytes.KnowableBy l · tr) { label := label', value := value' }).2
    (by simpa using hvalue)
  simpa [Bytes.KnowableBy] using this

/-- Port of `make_keypackage_ref_is_knowable_by`. -/
public
theorem makeKeypackageRef_knowableBy (tr: ProofTrace) (l: Label) (buf: Bytes) (res: Bytes)
  (h: makeKeypackageRef buf = .success res) (hbuf: buf.KnowableBy l tr):
  res.KnowableBy l tr
:=
  refHash_knowableBy tr l _ buf res h hbuf

/-- Port of `make_proposal_ref_is_knowable_by`. -/
public
theorem makeProposalRef_knowableBy (tr: ProofTrace) (l: Label) (buf: Bytes) (res: Bytes)
  (h: makeProposalRef buf = .success res) (hbuf: buf.KnowableBy l tr):
  res.KnowableBy l tr
:=
  refHash_knowableBy tr l _ buf res h hbuf

end MLS
