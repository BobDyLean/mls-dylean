module

public import MLS.TreeDEM.Code.Message.Transcript
public import MLS.TreeKEM.Code.KeySchedule
public import MLS.Test.FromExt.CryptoBasics
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.TranscriptHashes`.
-/

namespace MLS.Test.FromExt.TranscriptHashes

open Comparse
open MLS MLS.TreeKEM MLS.TreeDEM
open MLS.Test
open MLS.Test.FromExt.CryptoBasics

/-- Port of `test_transcript_hashes_one`. -/
@[expose]
public
def testTranscriptHashesOne (t: TranscriptHashesTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    let some authenticatedContent := parse AuthenticatedContent.mf (← hexStringToBytes t.authenticatedContent)
      | throw (IO.userError "authenticated_content: parse failed")
    if h: authenticatedContent.content.content.contentType == .commit then
      let confirmationKey ← hexStringToBytes t.confirmationKey
      let interimTranscriptHashBefore ← hexStringToBytes t.interimTranscriptHashBefore
      let confirmedTranscriptHashAfter ← extractResult (computeConfirmedTranscriptHash {
        wireFormat := authenticatedContent.wireFormat
        content := authenticatedContent.content
        signature := authenticatedContent.auth.signature
      } interimTranscriptHashBefore)
      let confirmationTag ← extractResult (computeConfirmationTag confirmationKey confirmedTranscriptHashAfter)
      let interimTranscriptHashAfter ← extractResult (computeInterimTranscriptHash (authenticatedContent.auth.confirmationTag.get h).val confirmedTranscriptHashAfter)
      checkEqual "confirmed_transcript_hash_after" bytesToHexString (← hexStringToBytes t.confirmedTranscriptHashAfter) confirmedTranscriptHashAfter
      checkEqual "interim_transcript_hash_after" bytesToHexString (← hexStringToBytes t.interimTranscriptHashAfter) interimTranscriptHashAfter
      checkEqual "confirmation_tag" bytesToHexString (authenticatedContent.auth.confirmationTag.get h).val confirmationTag
      pure true
    else
      throw (IO.userError "test_transcript_hashes_one: not a commit")

/-- Port of `test_transcript_hashes`. -/
@[expose]
public
def testTranscriptHashes: List TranscriptHashesTest → IO Nat :=
  testList "Transcript Hashes" testTranscriptHashesOne

end MLS.Test.FromExt.TranscriptHashes
