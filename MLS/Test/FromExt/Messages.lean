import MLS.TreeDEM.NetworkTypes
import MLS.Test.Types
import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.Messages`.
-/

namespace MLS.Test.FromExt.Messages

open Comparse
open MLS MLS.TreeSync MLS.TreeKEM MLS.Bootstrap MLS.TreeDEM
open MLS.Test

attribute [local instance] bytesLikeByteArray

/-- Port of `check_mls_welcome`. -/
def checkMlsWelcome (mlsWelcome: String): IO Unit := do
  let mlsWelcome ← hexStringToBytes mlsWelcome
  match parse MlsMessage.mf mlsWelcome with
  | none => throw (IO.userError "malformed mls_welcome")
  | some x => do
    match x with
    | .mls10 (.welcome _) => pure ()
    | _ => throw (IO.userError "mls_welcome don't contain a Welcome")
    checkEqual "mls_welcome" bytesToHexString mlsWelcome (serialize MlsMessage.mf x)

/-- Port of `check_mls_group_info`. -/
def checkMlsGroupInfo (mlsGroupInfo: String): IO Unit := do
  let mlsGroupInfo ← hexStringToBytes mlsGroupInfo
  match parse MlsMessage.mf mlsGroupInfo with
  | none => throw (IO.userError "malformed mls_group_info")
  | some x => do
    match x with
    | .mls10 (.groupInfo _) => pure ()
    | _ => throw (IO.userError "mls_group_info don't contain a GroupInfo")
    checkEqual "mls_group_info" bytesToHexString mlsGroupInfo (serialize MlsMessage.mf x)

/-- Port of `check_mls_key_package`. -/
def checkMlsKeyPackage (mlsKeyPackage: String): IO Unit := do
  let mlsKeyPackage ← hexStringToBytes mlsKeyPackage
  match parse MlsMessage.mf mlsKeyPackage with
  | none => throw (IO.userError "malformed mls_key_package")
  | some x => do
    match x with
    | .mls10 (.keyPackage _) => pure ()
    | _ => throw (IO.userError "mls_key_package don't contain a KeyPackage")
    checkEqual "mls_key_package" bytesToHexString mlsKeyPackage (serialize MlsMessage.mf x)

/-- Port of `check_ratchet_tree`. -/
def checkRatchetTree (ratchetTree: String): IO Unit := do
  let ratchetTree ← hexStringToBytes ratchetTree
  match parse (RatchetTree.mf tkt) ratchetTree with
  | none => throw (IO.userError "malformed ratchet_tree")
  | some x =>
    checkEqual "ratchet_tree" bytesToHexString ratchetTree (serialize (RatchetTree.mf tkt) x)

/-- Port of `check_group_secrets`. -/
def checkGroupSecrets (groupSecrets: String): IO Unit := do
  let groupSecrets ← hexStringToBytes groupSecrets
  match parse GroupSecrets.mf groupSecrets with
  | none => throw (IO.userError "malformed group_secrets")
  | some x =>
    checkEqual "group_secrets" bytesToHexString groupSecrets (serialize GroupSecrets.mf x)

/-- Port of `check_add_proposal`. -/
def checkAddProposal (addProposal: String): IO Unit := do
  let addProposal ← hexStringToBytes addProposal
  match parse Add.mf addProposal with
  | none => throw (IO.userError "malformed add")
  | some x =>
    checkEqual "add" bytesToHexString addProposal (serialize Add.mf x)

/-- Port of `check_update_proposal`. -/
def checkUpdateProposal (updateProposal: String): IO Unit := do
  let updateProposal ← hexStringToBytes updateProposal
  match parse Update.mf updateProposal with
  | none => throw (IO.userError "malformed update")
  | some x =>
    checkEqual "update" bytesToHexString updateProposal (serialize Update.mf x)

/-- Port of `check_remove_proposal`. -/
def checkRemoveProposal (removeProposal: String): IO Unit := do
  let removeProposal ← hexStringToBytes removeProposal
  match parse Remove.mf removeProposal with
  | none => throw (IO.userError "malformed remove")
  | some x =>
    checkEqual "remove" bytesToHexString removeProposal (serialize Remove.mf x)

/-- Port of `check_pre_shared_key_proposal`. -/
def checkPreSharedKeyProposal (preSharedKeyProposal: String): IO Unit := do
  let preSharedKeyProposal ← hexStringToBytes preSharedKeyProposal
  match parse PreSharedKey.mf preSharedKeyProposal with
  | none => throw (IO.userError "malformed pre_shared_key")
  | some x =>
    checkEqual "pre_shared_key" bytesToHexString preSharedKeyProposal (serialize PreSharedKey.mf x)

/-- Port of `check_reinit_proposal`. -/
def checkReinitProposal (reinitProposal: String): IO Unit := do
  let reinitProposal ← hexStringToBytes reinitProposal
  match parse Reinit.mf reinitProposal with
  | none => throw (IO.userError "malformed reinit")
  | some x =>
    checkEqual "reinit" bytesToHexString reinitProposal (serialize Reinit.mf x)

/-- Port of `check_external_init_proposal`. -/
def checkExternalInitProposal (externalInitProposal: String): IO Unit := do
  let externalInitProposal ← hexStringToBytes externalInitProposal
  match parse ExternalInit.mf externalInitProposal with
  | none => throw (IO.userError "malformed external_init")
  | some x =>
    checkEqual "external_init" bytesToHexString externalInitProposal (serialize ExternalInit.mf x)

/-- Port of `check_group_context_extensions_proposal`. -/
def checkGroupContextExtensionsProposal (groupContextExtensionsProposal: String): IO Unit := do
  let groupContextExtensionsProposal ← hexStringToBytes groupContextExtensionsProposal
  match parse GroupContextExtensions.mf groupContextExtensionsProposal with
  | none => throw (IO.userError "malformed group_context_extensions")
  | some x =>
    checkEqual "group_context_extensions" bytesToHexString groupContextExtensionsProposal (serialize GroupContextExtensions.mf x)

/-- Port of `check_commit`. -/
def checkCommit (commit: String): IO Unit := do
  let commit ← hexStringToBytes commit
  match parse Commit.mf commit with
  | none => throw (IO.userError "malformed commit")
  | some x =>
    checkEqual "commit" bytesToHexString commit (serialize Commit.mf x)

/-- Port of `check_public_message_application`. -/
def checkPublicMessageApplication (publicMessage: String): IO Unit := do
  let publicMessage ← hexStringToBytes publicMessage
  match parse MlsMessage.mf publicMessage with
  | none => throw (IO.userError "malformed public_message_application")
  | some x => do
    match x with
    | .mls10 (.publicMessage y) =>
      if y.content.content.contentType == .application then pure ()
      else throw (IO.userError "public_message_application don't contain application")
    | _ => throw (IO.userError "public_message_application don't contain a PublicMessage")
    checkEqual "public_message_application" bytesToHexString publicMessage (serialize MlsMessage.mf x)

/-- Port of `check_public_message_proposal`. -/
def checkPublicMessageProposal (publicMessage: String): IO Unit := do
  let publicMessage ← hexStringToBytes publicMessage
  match parse MlsMessage.mf publicMessage with
  | none => throw (IO.userError "malformed public_message_proposal")
  | some x => do
    match x with
    | .mls10 (.publicMessage y) =>
      if y.content.content.contentType == .proposal then pure ()
      else throw (IO.userError "public_message_proposal don't contain proposal")
    | _ => throw (IO.userError "public_message_proposal don't contain a PublicMessage")
    checkEqual "public_message_proposal" bytesToHexString publicMessage (serialize MlsMessage.mf x)

/-- Port of `check_public_message_commit`. -/
def checkPublicMessageCommit (publicMessage: String): IO Unit := do
  let publicMessage ← hexStringToBytes publicMessage
  match parse MlsMessage.mf publicMessage with
  | none => throw (IO.userError "malformed public_message_commit")
  | some x => do
    match x with
    | .mls10 (.publicMessage y) =>
      if y.content.content.contentType == .commit then pure ()
      else throw (IO.userError "public_message_commit don't contain commit")
    | _ => throw (IO.userError "public_message_commit don't contain a PublicMessage")
    checkEqual "public_message_commit" bytesToHexString publicMessage (serialize MlsMessage.mf x)

/-- Port of `check_private_message`. -/
def checkPrivateMessage (privateMessage: String): IO Unit := do
  let privateMessage ← hexStringToBytes privateMessage
  match parse MlsMessage.mf privateMessage with
  | none => throw (IO.userError "malformed private_message")
  | some x => do
    match x with
    | .mls10 (.privateMessage _) => pure ()
    | _ => throw (IO.userError "private_message don't contain a PrivateMessage")
    checkEqual "private_message" bytesToHexString privateMessage (serialize MlsMessage.mf x)

/-- Port of `test_messages_one`. -/
def testMessagesOne (t: MessagesTest): IO Bool := do
  checkMlsWelcome t.mlsWelcome
  checkMlsGroupInfo t.mlsGroupInfo
  checkMlsKeyPackage t.mlsKeyPackage
  checkRatchetTree t.ratchetTree
  checkGroupSecrets t.groupSecrets
  checkAddProposal t.addProposal
  checkUpdateProposal t.updateProposal
  checkRemoveProposal t.removeProposal
  checkPreSharedKeyProposal t.preSharedKeyProposal
  checkReinitProposal t.reInitProposal
  checkExternalInitProposal t.externalInitProposal
  checkGroupContextExtensionsProposal t.groupContextExtensionsProposal
  checkCommit t.commit
  checkPublicMessageApplication t.publicMessageApplication
  checkPublicMessageProposal t.publicMessageProposal
  checkPublicMessageCommit t.publicMessageCommit
  checkPrivateMessage t.privateMessage
  pure true

/-- Port of `test_messages`. -/
def testMessages: List MessagesTest → IO Nat :=
  testList "Messages" testMessagesOne

end MLS.Test.FromExt.Messages
