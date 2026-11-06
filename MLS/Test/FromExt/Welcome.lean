module

public import MLS.TreeDEM.Code.NetworkTypes
public import MLS.Bootstrap.Code.Welcome
public import MLS.TreeKEM.Code.KeySchedule
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.Welcome`.
-/

namespace MLS.Test.FromExt.Welcome

open Comparse
open MLS MLS.TreeKEM MLS.TreeDEM MLS.Bootstrap
open MLS.Test

/-- Port of `test_welcome_one`. -/
@[expose]
public
def testWelcomeOne (t: WelcomeTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs

    let initPriv ← extractResult (mkHpkePrivateKey (← hexStringToBytes t.initPriv) "test_welcome_one" "init_priv")
    let signerPub ← hexStringToBytes t.signerPub
    let keyPackage: KeyPackage ByteArray TreeKEM.tkt ←
      match parse MlsMessage.mf (← hexStringToBytes t.keyPackage) with
      | none => throw (IO.userError "test_welcome_one: malformed key package")
      | some (.mls10 (.keyPackage kp)) => pure kp
      | some _ => throw (IO.userError "test_welcome_one: message don't contain key package")
    let welcome: Welcome ByteArray ←
      match parse MlsMessage.mf (← hexStringToBytes t.welcome) with
      | none => throw (IO.userError "test_welcome_one: malformed welcome")
      | some (.mls10 (.welcome welcome)) => pure welcome
      | some _ => throw (IO.userError "test_welcome_one: message don't contain welcome")

    let kpRef ← extractResult (makeKeypackageRef (serializeNE (KeyPackage.mf TreeKEM.tkt) keyPackage))

    let (groupSecrets, _) ← extractResult (decryptGroupSecrets welcome (fun ref => if ref = kpRef then some initPriv else none) (fun x => pure x))
    let groupInfo ← extractResult (decryptGroupInfo groupSecrets.joinerSecret.val [] welcome.encryptedGroupInfo.val)

    if !verifyWelcomeGroupInfo signerPub groupInfo then
      throw (IO.userError "test_welcome_one: bad signature")

    let gc := groupInfo.tbs.groupContext
    let groupContext ← genGroupContext (CryptoBytes.ciphersuite ByteArray) gc.groupId.val gc.epoch.toNat gc.treeHash.val gc.confirmedTranscriptHash.val
    let joinerSecret := groupSecrets.joinerSecret.val
    let epochSecret ← extractResult (secretJoinerToEpoch joinerSecret [] groupContext)
    let confirmationKey ← extractResult (secretEpochToConfirmation epochSecret)
    let confirmationTag ← extractResult (computeConfirmationTag confirmationKey gc.confirmedTranscriptHash.val)
    checkEqual "confirmation_tag" bytesToHexString groupInfo.tbs.confirmationTag.val confirmationTag
    pure true

/-- Port of `test_welcome`. -/
@[expose]
public
def testWelcome: List WelcomeTest → IO Nat :=
  testList "Welcome" testWelcomeOne

end MLS.Test.FromExt.Welcome
