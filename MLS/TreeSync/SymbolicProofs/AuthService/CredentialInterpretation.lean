module

public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import MLS.Common.Proofs.Crypto.Derived
public import MLS.Symbolic.Code.Symbolic
import all MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation

/-!
Port of the lemmas of `MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation`.

Port-specific differences:
- MLS*'s `Some?` refinements and `match`es on `principal_to_credential p` are success hypotheses
  (`principalToCredential p = some cred`).
-/

namespace MLS.TreeSync

open Comparse
open MLS
open DY (Participant)

/-- Port of `principal_to_credential_to_principal`. -/
public
theorem credentialToPrincipal_principalToCredential {Bytes: Type} [BytesLike Bytes]
  (p: Participant) (cred: Credential Bytes)
  (h: principalToCredential p = some cred):
  credentialToPrincipal cred = some p
:= by
  simp only [principalToCredential] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  rename_i identity hid
  have := (mkMlsBytes_eq_success _ _ _ _).1 hid
  subst h
  simp only [credentialToPrincipal, ← this]
  exact parse_serializeNE _ p

section Symbolic

open DY

variable [HasSymbolicInvariants]

/-- Port of `is_publishable_principal_to_credential`. -/
public
theorem principalToCredential_wf (tr: ProofTrace) (p: Participant) (cred: Credential Bytes)
  (h: principalToCredential p = some cred):
  Credential.mf.wf (Bytes.Publishable · tr) cred
:= by
  simp only [principalToCredential] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  rename_i identity hid
  have := (mkMlsBytes_eq_success _ _ _ _).1 hid
  subst h
  simp only [Credential.mf.wf_eq, ← this]
  exact (pred_serializeNE_iff NonExtensibleMessageFormat.unboundedString (Bytes.Publishable · tr) p).2
    (NonExtensibleMessageFormat.unboundedString.wf_eq _ p)

end Symbolic

end MLS.TreeSync
