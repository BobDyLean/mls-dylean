import MLS.Common.Code.Crypto.Derived
import MLS.TreeKEM.Code.NetworkTypes
import MLS.TreeKEM.Code.PSK

/-!
Port of `MLS.TreeKEM.KeySchedule`.

Port-specific differences:
- The secrets are `Bytes` (MLS*'s `lbytes bytes (kdf_length #bytes)`, see `MLS.Crypto.Builtins`).
- Labels are `String`s (MLS*'s `valid_label`, see `MLS.Crypto.Derived`).
-/

namespace MLS.TreeKEM

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `secret_init_to_joiner`. -/
def secretInitToJoiner (initSecret: Bytes) (optCommitSecret: Option Bytes) (groupContext: GroupContext Bytes): Result Bytes := do
  let commitSecret :=
    match optCommitSecret with
    | some commitSecret => commitSecret
    | none => zeroVector
  let prk ← CryptoBytes.kdfExtract initSecret commitSecret
  expandWithLabel prk "joiner" (serializeNE GroupContext.mf groupContext) (CryptoBytes.kdfLength Bytes)

/--
Port of `secret_joiner_to_welcome_internal`.
this version is tested in the test vectors
-/
def secretJoinerToWelcomeInternal (joinerSecret: Bytes) (pskSecret: Bytes): Result Bytes := do
  let prk ← CryptoBytes.kdfExtract joinerSecret pskSecret
  deriveSecret prk "welcome"

/-- Port of `secret_joiner_to_welcome`. -/
def secretJoinerToWelcome (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)): Result Bytes := do
  let pskSecret ← computePskSecret psks
  secretJoinerToWelcomeInternal joinerSecret pskSecret

/--
Port of `secret_joiner_to_epoch_internal`.
this version is tested in the test vectors
-/
def secretJoinerToEpochInternal (joinerSecret: Bytes) (pskSecret: Bytes) (groupContext: GroupContext Bytes): Result Bytes := do
  let prk ← CryptoBytes.kdfExtract joinerSecret pskSecret
  expandWithLabel prk "epoch" (serializeNE GroupContext.mf groupContext) (CryptoBytes.kdfLength Bytes)

/-- Port of `secret_joiner_to_epoch`. -/
def secretJoinerToEpoch (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes): Result Bytes := do
  let pskSecret ← computePskSecret psks
  secretJoinerToEpochInternal joinerSecret pskSecret groupContext

/-- Port of `secret_epoch_to_sender_data`. -/
def secretEpochToSenderData (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "sender data"

/-- Port of `secret_epoch_to_encryption`. -/
def secretEpochToEncryption (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "encryption"

/-- Port of `secret_epoch_to_exporter`. -/
def secretEpochToExporter (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "exporter"

/-- Port of `secret_epoch_to_external`. -/
def secretEpochToExternal (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "external"

/-- Port of `secret_epoch_to_confirmation`. -/
def secretEpochToConfirmation (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "confirm"

/-- Port of `secret_epoch_to_membership`. -/
def secretEpochToMembership (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "membership"

/-- Port of `secret_epoch_to_resumption`. -/
def secretEpochToResumption (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "resumption"

/-- Port of `secret_epoch_to_authentication`. -/
def secretEpochToAuthentication (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "authentication"

/-- Port of `secret_epoch_to_init`. -/
def secretEpochToInit (epochSecret: Bytes): Result Bytes :=
  deriveSecret epochSecret "init"

/-- Port of `secret_external_to_keypair`. -/
def secretExternalToKeypair (externalSecret: Bytes): Result (Bytes × Bytes) :=
  CryptoBytes.hpkeGenKeypair externalSecret

/-- Port of `mls_exporter`. -/
def mlsExporter (exporterSecret: Bytes) (label: String) (context: Bytes) (len: Nat): Result Bytes := do
  let derivedSecret ← deriveSecret exporterSecret label
  let hashedContext ← CryptoBytes.hashHash context
  expandWithLabel derivedSecret "exported" hashedContext len

/-- Port of `compute_confirmation_tag`. -/
def computeConfirmationTag (confirmationKey: Bytes) (confirmedTranscriptHash: Bytes): Result Bytes :=
  CryptoBytes.hmacHmac confirmationKey confirmedTranscriptHash

end MLS.TreeKEM
