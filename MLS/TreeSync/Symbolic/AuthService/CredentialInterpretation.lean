module

public import MLS.Common.Code.Crypto.Derived
public import DY.Actions.PersistentLocalState

/-!
Port of `MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation`:
how principals are encoded in (basic) credentials.

Port-specific differences:
- Principals are DyLean's `Participant`s, serialized as strings (`slowString`, as DyLean's local states),
  instead of DY*'s `ps_principal`.
- The lemmas (`principal_to_credential_to_principal`, `is_publishable_principal_to_credential`)
  are not ported yet.
-/

namespace MLS.TreeSync

open Comparse
open MLS
open DY (Participant)

variable {Bytes: Type} [BytesLike Bytes]

/-- Port of `credential_to_principal`. -/
public
def credentialToPrincipal (cred: Credential Bytes): Option Participant :=
  match cred with
  | .basic identity => (NonExtensibleMessageFormat.slowString (Bytes := Bytes)).toExtensible.parse identity.val
  | _ => none

/-- Port of `principal_to_credential`. -/
public
def principalToCredential (p: Participant): Option (Credential Bytes) :=
  let pBytes: Bytes := NonExtensibleMessageFormat.slowString.toExtensible.serialize p
  match mkMlsBytes pBytes "principal_to_credential" "p_bytes" with
  | .success identity => some (.basic identity)
  | _ => none

end MLS.TreeSync
