module

public import MLS.TreeKEM.Code.KeySchedule
public import MLS.TreeKEM.Code.API.KeySchedule.Types

/-!
Port of `MLS.TreeKEM.API.KeySchedule`.

Port-specific differences:
- The namespace is `MLS.TreeKEM.API.KeySchedule` (instead of `MLS.TreeKEM`), as its names are reused by `MLS.TreeKEM.API`.
- `export` is a Lean keyword: the function is named `«export»`.
-/

namespace MLS.TreeKEM.API.KeySchedule

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `create_from_epoch_secret`. -/
public
def createFromEpochSecret (epochSecret: Bytes) (groupContext: GroupContext Bytes):
  Result (TreeKEMKeyscheduleState Bytes × Bytes)
:= do
  let senderDataSecret ← secretEpochToSenderData epochSecret
  let encryptionSecret ← secretEpochToEncryption epochSecret
  let exporterSecret ← secretEpochToExporter epochSecret
  let externalSecret ← secretEpochToExternal epochSecret
  let confirmationKey ← secretEpochToConfirmation epochSecret
  let confirmationTag ← computeConfirmationTag confirmationKey groupContext.confirmedTranscriptHash.val
  let membershipKey ← secretEpochToMembership epochSecret
  let resumptionPsk ← secretEpochToResumption epochSecret
  let epochAuthenticator ← secretEpochToAuthentication epochSecret
  let initSecret ← secretEpochToInit epochSecret
  pure ({
    epochKeys := {
      senderDataSecret
      exporterSecret
      externalSecret
      membershipKey
      resumptionPsk
      epochAuthenticator
      confirmationTag
    }
    initSecret
  }, encryptionSecret)

/-- Port of `create_from_joiner_secret`. -/
public
def createFromJoinerSecret (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes):
  Result (TreeKEMKeyscheduleState Bytes × Bytes)
:= do
  let epochSecret ← secretJoinerToEpoch joinerSecret psks groupContext
  createFromEpochSecret epochSecret groupContext

/-- Port of `secrets_for_welcome`. -/
public
structure SecretsForWelcome (Bytes: Type) where
  joinerSecret: Bytes
  welcomeSecret: Bytes

/-- Port of `commit`. -/
public
def commit (st: TreeKEMKeyscheduleState Bytes) (optCommitSecret: Option Bytes)
  (psks: List (PreSharedKeyId Bytes × Bytes)) (newGroupContext: GroupContext Bytes)
  : Result (TreeKEMKeyscheduleState Bytes × Bytes × SecretsForWelcome Bytes)
:= do
  let joinerSecret ← secretInitToJoiner st.initSecret optCommitSecret newGroupContext
  let epochSecret ← secretJoinerToEpoch joinerSecret psks newGroupContext
  let welcomeSecret ← secretJoinerToWelcome joinerSecret psks
  let (newSt, encryptionSecret) ← createFromEpochSecret epochSecret newGroupContext
  pure (newSt, encryptionSecret, {
    joinerSecret
    welcomeSecret
  })

/-- Port of `export`. -/
public
def «export» (st: TreeKEMKeyscheduleState Bytes) (label: String) (context: Bytes) (len: Nat): Result Bytes :=
  mlsExporter st.epochKeys.exporterSecret label context len

end MLS.TreeKEM.API.KeySchedule
