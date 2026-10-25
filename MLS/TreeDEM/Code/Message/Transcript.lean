import MLS.TreeDEM.Code.NetworkTypes
import MLS.Common.Code.Crypto.Derived

/-!
Port of `MLS.TreeDEM.Message.Transcript`.
-/

namespace MLS.TreeDEM

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/--
Port of `compute_confirmed_transcript_hash`.
MLS* fails when the content is not a commit (as an internal failure).
-/
def computeConfirmedTranscriptHash (txHashInput: ConfirmedTranscriptHashInput Bytes) (interimTranscriptHash: Bytes): Result Bytes :=
  match txHashInput.content.content.contentType with
  | .commit =>
    let serializedMsg := serializeNE ConfirmedTranscriptHashInput.mf txHashInput
    let hashInput := BytesLike.concat interimTranscriptHash serializedMsg
    CryptoBytes.hashHash hashInput
  | _ => Result.internalFailure "compute_confirmed_transcript_hash: should only be used on a commit message"

/-- Port of `compute_interim_transcript_hash`. -/
def computeInterimTranscriptHash (confirmationTag: Bytes) (confirmedTranscriptHash: Bytes): Result Bytes := do
  let confirmationTag ← mkMlsBytes confirmationTag "compute_interim_transcript_hash" "confirmation_tag"
  let serializedAuth := serializeNE InterimTranscriptHashInput.mf { confirmationTag }
  let hashInput := BytesLike.concat confirmedTranscriptHash serializedAuth
  CryptoBytes.hashHash hashInput

end MLS.TreeDEM
