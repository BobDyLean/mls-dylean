module

public import MLS.TreeSync.SymbolicSpec.AuthService
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey
public import MLS.TreeSync.Proofs.Invariants.AuthService

/-!
Port of the instantiation of the Authentication Service in `MLS.TreeSync.Symbolic.AuthService`.

Port-specific differences:
- DY*'s `on_trace` (`token.time < trace_length tr`) is weakened to `token.time ≤ tr.length` in `dyAsp`
  (DY* needs it for `prefix tr token.time`, which is total in DyLean), so that the current time is a valid token
  (see `MLS.TreeSync.verifyCredential`).
-/

namespace MLS.TreeSync

open DY
open MLS

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/--
Port of `dy_asp`.
Instantiation of the abstract "Authentication Service" for DY*.
The token is a a timestamp,
and the AS attests that the signature verification key belonged to that principal at that time.
-/
@[expose]
public
def dyAsp (tr: ProofTrace): ASParameters Bytes DyAsToken where
  credentialOk := fun (vk, cred) token =>
    match credentialToPrincipal cred with
    | none => False
    | some who =>
      token.time ≤ tr.length ∧
      IsSignatureKeyVk (tr.prefix token.time) who vk.val
  validSuccessor _ _ := True

/-- Port of `dy_asp_later`. -/
public
theorem dyAsp_later (tr1 tr2: ProofTrace) (inp: ASInput Bytes) (token: DyAsToken)
  : (dyAsp tr1).credentialOk inp token →
    tr1 ≤ tr2 →
    (dyAsp tr2).credentialOk inp token
:= by
  obtain ⟨vk, cred⟩ := inp
  intro h hle
  simp only [dyAsp] at h ⊢
  split at h <;> grind

grind_pattern dyAsp_later => tr1 ≤ tr2, (dyAsp tr1).credentialOk inp token
grind_pattern [grind_later] dyAsp_later => tr1 ≤ tr2, (dyAsp tr1).credentialOk inp token

/-- Port of `all_credentials_ok_later`. -/
public
theorem allCredentialsOk_later {tkt: TreeKEMTypes Bytes} {l: Nat} (tr1 tr2: ProofTrace)
  (ts: TreeSync Bytes tkt l) (ast: ASTokens DyAsToken l)
  : allCredentialsOk (dyAsp tr1) ts ast →
    tr1 ≤ tr2 →
    allCredentialsOk (dyAsp tr2) ts ast
:= by
  intro h hle
  apply allCredentialsOk_weaken (dyAsp tr2) ts ast _ h
  grind [asParametersWeaker]

grind_pattern allCredentialsOk_later => tr1 ≤ tr2, allCredentialsOk (dyAsp tr1) ts ast
grind_pattern [grind_later] allCredentialsOk_later => tr1 ≤ tr2, allCredentialsOk (dyAsp tr1) ts ast

/-- The AS attests that the signature key is a verification key of the principal of the credential. -/
public
theorem isSignatureKeyVk_of_credentialOk (tr: ProofTrace)
  (vk: SignaturePublicKey Bytes) (cred: Credential Bytes) (token: DyAsToken)
  (h: (dyAsp tr).credentialOk (vk, cred) token):
  ∃ who, credentialToPrincipal cred = some who ∧ IsSignatureKeyVk tr who vk.val
:= by
  simp only [dyAsp] at h
  split at h <;> grind

end MLS.TreeSync
