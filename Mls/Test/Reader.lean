import Lean.Data.Json
import Mls.Test.Types

/-!
Port of `MLS.Test.Reader` (an OCaml file in MLS*), using Lean's JSON library.
-/

namespace Mls.Test

open Lean

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
  | .messages => "test_vectors/data/messages.json"

def getTestsuite (testVectorsDir: System.FilePath) (typ: TestType): IO Testsuite := do
  let content ← IO.FS.readFile (testVectorsDir / getFilename typ)
  let json ← IO.ofExcept (Json.parse content)
  let l ← IO.ofExcept (json.getArr?.mapError (s!"get_testsuite: incorrect test vector format: {·}"))
  match typ with
  | .messages =>
    let tests ← IO.ofExcept (l.toList.mapM parseMessagesTest |>.mapError (s!"parse_messages_test: incorrect test vector format: {·}"))
    return .messagesTest tests

end Mls.Test
