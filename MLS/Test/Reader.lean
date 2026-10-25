import Lean.Data.Json
import MLS.Test.Types

/-!
Port of `MLS.Test.Reader` (an OCaml file in MLS*), using Lean's JSON library.
-/

namespace MLS.Test

open Lean

instance: FromJson UInt16 where
  fromJson? j := do
    let n ← j.getNat?
    if n < 2^16 then pure n.toUInt16 else throw s!"expected uint16, got {n}"

instance: FromJson UInt32 where
  fromJson? j := do
    let n ← j.getNat?
    if n < 2^32 then pure n.toUInt32 else throw s!"expected uint32, got {n}"

instance: FromJson UInt64 where
  fromJson? j := do
    let n ← j.getNat?
    if n < 2^64 then pure n.toUInt64 else throw s!"expected uint64, got {n}"

/-! ## Crypto Basics -/

def parseCryptoBasicsTest (json: Json): Except String CryptoBasicsTest := do
  let refHash ← json.getObjVal? "ref_hash"
  let expandWithLabel ← json.getObjVal? "expand_with_label"
  let deriveSecret ← json.getObjVal? "derive_secret"
  let deriveTreeSecret ← json.getObjVal? "derive_tree_secret"
  let signWithLabel ← json.getObjVal? "sign_with_label"
  let encryptWithLabel ← json.getObjVal? "encrypt_with_label"
  return {
    cipherSuite := ← json.getObjValAs? UInt16 "cipher_suite"
    refHash := {
      label := ← refHash.getObjValAs? String "label"
      value := ← refHash.getObjValAs? String "value"
      out := ← refHash.getObjValAs? String "out"
    }
    expandWithLabel := {
      secret := ← expandWithLabel.getObjValAs? String "secret"
      label := ← expandWithLabel.getObjValAs? String "label"
      context := ← expandWithLabel.getObjValAs? String "context"
      length := ← expandWithLabel.getObjValAs? UInt16 "length"
      out := ← expandWithLabel.getObjValAs? String "out"
    }
    deriveSecret := {
      secret := ← deriveSecret.getObjValAs? String "secret"
      label := ← deriveSecret.getObjValAs? String "label"
      out := ← deriveSecret.getObjValAs? String "out"
    }
    deriveTreeSecret := {
      secret := ← deriveTreeSecret.getObjValAs? String "secret"
      label := ← deriveTreeSecret.getObjValAs? String "label"
      generation := ← deriveTreeSecret.getObjValAs? UInt32 "generation"
      length := ← deriveTreeSecret.getObjValAs? UInt16 "length"
      out := ← deriveTreeSecret.getObjValAs? String "out"
    }
    signWithLabel := {
      priv := ← signWithLabel.getObjValAs? String "priv"
      pub := ← signWithLabel.getObjValAs? String "pub"
      content := ← signWithLabel.getObjValAs? String "content"
      label := ← signWithLabel.getObjValAs? String "label"
      signature := ← signWithLabel.getObjValAs? String "signature"
    }
    encryptWithLabel := {
      priv := ← encryptWithLabel.getObjValAs? String "priv"
      pub := ← encryptWithLabel.getObjValAs? String "pub"
      label := ← encryptWithLabel.getObjValAs? String "label"
      context := ← encryptWithLabel.getObjValAs? String "context"
      plaintext := ← encryptWithLabel.getObjValAs? String "plaintext"
      kemOutput := ← encryptWithLabel.getObjValAs? String "kem_output"
      ciphertext := ← encryptWithLabel.getObjValAs? String "ciphertext"
    }
  }

/-! ## Tree Validation -/

def parseTreeValidationTest (json: Json): Except String TreeValidationTest := do
  return {
    cipherSuite := ← json.getObjValAs? UInt16 "cipher_suite"
    tree := ← json.getObjValAs? String "tree"
    groupId := ← json.getObjValAs? String "group_id"
    resolutions := ← json.getObjValAs? (List (List UInt32)) "resolutions"
    treeHashes := ← json.getObjValAs? (List String) "tree_hashes"
  }

/-! ## Tree Operations -/

def parseTreeOperationsTest (json: Json): Except String TreeOperationsTest := do
  return {
    treeBefore := ← json.getObjValAs? String "tree_before"
    proposal := ← json.getObjValAs? String "proposal"
    proposalSender := ← json.getObjValAs? UInt32 "proposal_sender"
    treeAfter := ← json.getObjValAs? String "tree_after"
  }

/-! ## Key Schedule -/

def parseKeyscheduleTestEpoch (json: Json): Except String (KeyscheduleTestEpochInput × KeyscheduleTestEpochOutput) := do
  let get (field: String): Except String String := json.getObjValAs? String field
  let exporter ← json.getObjVal? "exporter"
  return ({
    treeHash := ← get "tree_hash"
    commitSecret := ← get "commit_secret"
    pskSecret := ← get "psk_secret"
    confirmedTranscriptHash := ← get "confirmed_transcript_hash"
    exporterLabel := ← exporter.getObjValAs? String "label"
    exporterContext := ← exporter.getObjValAs? String "context"
    exporterLength := ← exporter.getObjValAs? UInt32 "length"
  }, {
    groupContext := ← get "group_context"
    joinerSecret := ← get "joiner_secret"
    welcomeSecret := ← get "welcome_secret"
    initSecret := ← get "init_secret"
    senderDataSecret := ← get "sender_data_secret"
    encryptionSecret := ← get "encryption_secret"
    exporterSecret := ← get "exporter_secret"
    epochAuthenticator := ← get "epoch_authenticator"
    externalSecret := ← get "external_secret"
    confirmationKey := ← get "confirmation_key"
    membershipKey := ← get "membership_key"
    resumptionPsk := ← get "resumption_psk"
    externalPub := ← get "external_pub"
    exportedSecret := ← exporter.getObjValAs? String "secret"
  })

def parseKeyscheduleTest (json: Json): Except String KeyscheduleTest := do
  return {
    cipherSuite := ← json.getObjValAs? UInt16 "cipher_suite"
    groupId := ← json.getObjValAs? String "group_id"
    initialInitSecret := ← json.getObjValAs? String "initial_init_secret"
    epochs := ← (← json.getObjValAs? (List Json) "epochs").mapM parseKeyscheduleTestEpoch
  }

/-! ## Pre-Shared Keys -/

def parsePskTestPsk (json: Json): Except String PskTestPsk := do
  return {
    pskId := ← json.getObjValAs? String "psk_id"
    psk := ← json.getObjValAs? String "psk"
    pskNonce := ← json.getObjValAs? String "psk_nonce"
  }

def parsePskTest (json: Json): Except String PskTest := do
  return {
    cipherSuite := ← json.getObjValAs? UInt16 "cipher_suite"
    psks := ← (← json.getObjValAs? (List Json) "psks").mapM parsePskTestPsk
    pskSecret := ← json.getObjValAs? String "psk_secret"
  }

/-! ## Welcome -/

def parseWelcomeTest (json: Json): Except String WelcomeTest := do
  return {
    cipherSuite := ← json.getObjValAs? UInt16 "cipher_suite"
    initPriv := ← json.getObjValAs? String "init_priv"
    signerPub := ← json.getObjValAs? String "signer_pub"
    keyPackage := ← json.getObjValAs? String "key_package"
    welcome := ← json.getObjValAs? String "welcome"
  }

/-! ## TreeKEM -/

def parseTreeKEMLeafPathSecret (json: Json): Except String TreeKEMLeafPathSecret := do
  return {
    node := ← json.getObjValAs? UInt32 "node"
    pathSecret := ← json.getObjValAs? String "path_secret"
  }

def parseTreeKEMLeafPrivate (json: Json): Except String TreeKEMLeafPrivate := do
  return {
    index := ← json.getObjValAs? UInt32 "index"
    encryptionPriv := ← json.getObjValAs? String "encryption_priv"
    signaturePriv := ← json.getObjValAs? String "signature_priv"
    pathSecrets := ← (← json.getObjValAs? (List Json) "path_secrets").mapM parseTreeKEMLeafPathSecret
  }

def parseTreeKEMUpdatePath (json: Json): Except String TreeKEMUpdatePath := do
  return {
    sender := ← json.getObjValAs? UInt32 "sender"
    updatePath := ← json.getObjValAs? String "update_path"
    pathSecrets := ← json.getObjValAs? (List (Option String)) "path_secrets"
    commitSecret := ← json.getObjValAs? String "commit_secret"
    treeHashAfter := ← json.getObjValAs? String "tree_hash_after"
  }

def parseTreeKEMTest (json: Json): Except String TreeKEMTest := do
  return {
    cipherSuite := ← json.getObjValAs? UInt16 "cipher_suite"
    groupId := ← json.getObjValAs? String "group_id"
    epoch := ← json.getObjValAs? UInt64 "epoch"
    confirmedTranscriptHash := ← json.getObjValAs? String "confirmed_transcript_hash"
    ratchetTree := ← json.getObjValAs? String "ratchet_tree"
    leavesPrivate := ← (← json.getObjValAs? (List Json) "leaves_private").mapM parseTreeKEMLeafPrivate
    updatePaths := ← (← json.getObjValAs? (List Json) "update_paths").mapM parseTreeKEMUpdatePath
  }

/-! ## Messages -/

def parseMessagesTest (json: Json): Except String MessagesTest := do
  let get (field: String): Except String String := json.getObjValAs? String field
  return {
    mlsWelcome := ← get "mls_welcome"
    mlsGroupInfo := ← get "mls_group_info"
    mlsKeyPackage := ← get "mls_key_package"
    ratchetTree := ← get "ratchet_tree"
    groupSecrets := ← get "group_secrets"
    addProposal := ← get "add_proposal"
    updateProposal := ← get "update_proposal"
    removeProposal := ← get "remove_proposal"
    preSharedKeyProposal := ← get "pre_shared_key_proposal"
    reInitProposal := ← get "re_init_proposal"
    externalInitProposal := ← get "external_init_proposal"
    groupContextExtensionsProposal := ← get "group_context_extensions_proposal"
    commit := ← get "commit"
    publicMessageApplication := ← get "public_message_application"
    publicMessageProposal := ← get "public_message_proposal"
    publicMessageCommit := ← get "public_message_commit"
    privateMessage := ← get "private_message"
  }

/-! ## Final functions -/

def getFilename: TestType → String
  | .cryptoBasics => "test_vectors/data/crypto-basics.json"
  | .treeValidation => "test_vectors/data/tree-validation.json"
  | .treeOperations => "test_vectors/data/tree-operations.json"
  | .keySchedule => "test_vectors/data/key-schedule.json"
  | .preSharedKeys => "test_vectors/data/psk_secret.json"
  | .welcome => "test_vectors/data/welcome.json"
  | .treekem => "test_vectors/data/treekem.json"
  | .messages => "test_vectors/data/messages.json"

def getTestsuite (testVectorsDir: System.FilePath) (typ: TestType): IO Testsuite := do
  let content ← IO.FS.readFile (testVectorsDir / getFilename typ)
  let json ← IO.ofExcept (Json.parse content)
  let l ← IO.ofExcept (json.getArr?.mapError (s!"get_testsuite: incorrect test vector format: {·}"))
  match typ with
  | .cryptoBasics =>
    let tests ← IO.ofExcept (l.toList.mapM parseCryptoBasicsTest |>.mapError (s!"parse_crypto_basics_test: incorrect test vector format: {·}"))
    return .cryptoBasicsTest tests
  | .treeValidation =>
    let tests ← IO.ofExcept (l.toList.mapM parseTreeValidationTest |>.mapError (s!"parse_tree_validation_test: incorrect test vector format: {·}"))
    return .treeValidationTest tests
  | .treeOperations =>
    let tests ← IO.ofExcept (l.toList.mapM parseTreeOperationsTest |>.mapError (s!"parse_tree_operations_test: incorrect test vector format: {·}"))
    return .treeOperationsTest tests
  | .keySchedule =>
    let tests ← IO.ofExcept (l.toList.mapM parseKeyscheduleTest |>.mapError (s!"parse_keyschedule_test: incorrect test vector format: {·}"))
    return .keyScheduleTest tests
  | .preSharedKeys =>
    let tests ← IO.ofExcept (l.toList.mapM parsePskTest |>.mapError (s!"parse_psk_test: incorrect test vector format: {·}"))
    return .preSharedKeysTest tests
  | .welcome =>
    let tests ← IO.ofExcept (l.toList.mapM parseWelcomeTest |>.mapError (s!"parse_welcome_test: incorrect test vector format: {·}"))
    return .welcomeTest tests
  | .treekem =>
    let tests ← IO.ofExcept (l.toList.mapM parseTreeKEMTest |>.mapError (s!"parse_treekem_test: incorrect test vector format: {·}"))
    return .treekemTest tests
  | .messages =>
    let tests ← IO.ofExcept (l.toList.mapM parseMessagesTest |>.mapError (s!"parse_messages_test: incorrect test vector format: {·}"))
    return .messagesTest tests

end MLS.Test
