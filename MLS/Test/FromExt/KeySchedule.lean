module

public import MLS.TreeKEM.Code.KeySchedule
public import MLS.Test.FromExt.CryptoBasics
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.KeySchedule`.

Port-specific differences:
- The cipher suite P-521 (not supported by MLS*) is skipped: see `testKeyscheduleOne`.
-/

namespace MLS.Test.FromExt.KeySchedule

open Comparse
open MLS MLS.TreeKEM
open MLS.Test
open MLS.Test.FromExt.CryptoBasics

section CryptoBytes

variable [CryptoBytes ByteArray]

/-- Port of `gen_epoch_output`. -/
@[expose]
public
def genEpochOutput (groupId: String) (lastInitSecret: String) (epoch: Nat) (inp: KeyscheduleTestEpochInput):
  IO KeyscheduleTestEpochOutput
:= do
  let commitSecret ← hexStringToBytes inp.commitSecret
  let pskSecret ← hexStringToBytes inp.pskSecret

  let groupContext ← genGroupContext (CryptoBytes.ciphersuite ByteArray) (← hexStringToBytes groupId) epoch (← hexStringToBytes inp.treeHash) (← hexStringToBytes inp.confirmedTranscriptHash)
  let lastInitSecret ← hexStringToBytes lastInitSecret
  let joinerSecret ← extractResult (secretInitToJoiner lastInitSecret (some commitSecret) groupContext)
  let welcomeSecret ← extractResult (secretJoinerToWelcomeInternal joinerSecret pskSecret)
  let epochSecret ← extractResult (secretJoinerToEpochInternal joinerSecret pskSecret groupContext)
  let initSecret ← extractResult (secretEpochToInit epochSecret)
  let senderDataSecret ← extractResult (secretEpochToSenderData epochSecret)
  let encryptionSecret ← extractResult (secretEpochToEncryption epochSecret)
  let exporterSecret ← extractResult (secretEpochToExporter epochSecret)
  let epochAuthenticator ← extractResult (secretEpochToAuthentication epochSecret)
  let externalSecret ← extractResult (secretEpochToExternal epochSecret)
  let confirmationKey ← extractResult (secretEpochToConfirmation epochSecret)
  let membershipKey ← extractResult (secretEpochToMembership epochSecret)
  let resumptionPsk ← extractResult (secretEpochToResumption epochSecret)
  let externalPub := (← extractResult (secretExternalToKeypair externalSecret)).2
  let exportedSecret ←
    if !(inp.exporterLabel.all (fun (c: Char) => c.toNat < 128) && inp.exporterLabel.length < 2^30 - 8) then
      throw (IO.userError "gen_epoch_output: exporter label is not ascii")
    else
      extractResult (mlsExporter exporterSecret inp.exporterLabel (← hexStringToBytes inp.exporterContext) inp.exporterLength.toNat)

  pure {
    groupContext := bytesToHexString (serializeNE GroupContext.mf groupContext)
    joinerSecret := bytesToHexString joinerSecret
    welcomeSecret := bytesToHexString welcomeSecret
    initSecret := bytesToHexString initSecret
    senderDataSecret := bytesToHexString senderDataSecret
    encryptionSecret := bytesToHexString encryptionSecret
    exporterSecret := bytesToHexString exporterSecret
    epochAuthenticator := bytesToHexString epochAuthenticator
    externalSecret := bytesToHexString externalSecret
    confirmationKey := bytesToHexString confirmationKey
    membershipKey := bytesToHexString membershipKey
    resumptionPsk := bytesToHexString resumptionPsk
    externalPub := bytesToHexString externalPub
    exportedSecret := bytesToHexString exportedSecret
  }

/-- Port of `gen_list_epoch_output_aux`. -/
@[expose]
public
def genListEpochOutputAux (groupId: String) (lastInitSecret: String) (epoch: Nat):
  List KeyscheduleTestEpochInput → IO (List KeyscheduleTestEpochOutput)
  | [] => pure []
  | h::t => do
    let outputHead ← genEpochOutput groupId lastInitSecret epoch h
    let outputTail ← genListEpochOutputAux groupId outputHead.initSecret (epoch + 1) t
    pure (outputHead::outputTail)

/-- Port of `gen_list_epoch_output`. -/
@[expose]
public
def genListEpochOutput (groupId: String) (initialInitSecret: String) (l: List KeyscheduleTestEpochInput):
  IO (List KeyscheduleTestEpochOutput)
:=
  genListEpochOutputAux groupId initialInitSecret 0 l

end CryptoBytes

/-- Port of `test_keyschedule_one`. -/
@[expose]
public
def testKeyscheduleOne (t: KeyscheduleTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success .mls_256_dhkemp521_aes256gcm_sha512_p521 =>
    -- Unsupported: OpenSSL's `DeriveKeyPair` requires `Nsk` (66) bytes of `ikm`,
    -- but `external_secret` has `Nh` (64) bytes (MLS*'s `hpke_ikm` has the same requirement).
    pure false
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    let (inputs, expectedOutputs) := t.epochs.unzip
    let ourOutputs ← genListEpochOutput t.groupId t.initialInitSecret inputs
    for (eOut, oOut) in expectedOutputs.zip ourOutputs do
      let check (name: String) (field: KeyscheduleTestEpochOutput → String): IO Unit := do
        checkEqual name bytesToHexString (← hexStringToBytes (field eOut)) (← hexStringToBytes (field oOut))
      check "group_context" (·.groupContext)
      check "joiner_secret" (·.joinerSecret)
      check "welcome_secret" (·.welcomeSecret)
      check "init_secret" (·.initSecret)
      check "sender_data_secret" (·.senderDataSecret)
      check "encryption_secret" (·.encryptionSecret)
      check "exporter_secret" (·.exporterSecret)
      check "epoch_authenticator" (·.epochAuthenticator)
      check "external_secret" (·.externalSecret)
      check "confirmation_key" (·.confirmationKey)
      check "membership_key" (·.membershipKey)
      check "resumption_psk" (·.resumptionPsk)
      check "external_pub" (·.externalPub)
      check "exported_secret" (·.exportedSecret)
    pure true

/-- Port of `test_keyschedule`. -/
@[expose]
public
def testKeyschedule: List KeyscheduleTest → IO Nat :=
  testList "KeySchedule" testKeyscheduleOne

end MLS.Test.FromExt.KeySchedule
