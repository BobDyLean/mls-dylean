module

public import MLS.TreeDEM.Code.Message.Framing
public import MLS.Glue.Code.NetworkBinder
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.SecretTree`.
-/

namespace MLS.Test.FromExt.SecretTree

open Comparse
open MLS MLS.TreeDEM
open MLS.Test

section CryptoBytes

variable [CryptoBytes ByteArray]

/-- Port of `test_sender_data`. -/
public
def testSenderData (t: SecretTreeSenderData): IO Unit := do
  let senderDataSecret ← hexStringToBytes t.senderDataSecret
  let ciphertext ← hexStringToBytes t.ciphertext

  let ciphertextSample := getCiphertextSample ciphertext
  let (senderDataKey, senderDataNonce) ← extractResult (senderDataKeyNonce ciphertextSample senderDataSecret)
  checkEqual "sender_data_key" bytesToHexString (← hexStringToBytes t.key) senderDataKey
  checkEqual "sender_data_nonce" bytesToHexString (← hexStringToBytes t.nonce) senderDataNonce

/-- Port of `test_leaf`. -/
public
def testLeaf (levels: Nat) (leafInd: Nat) (encryptionSecret: String) (t: SecretTreeLeaf): IO Unit := do
  let encryptionSecret ← hexStringToBytes encryptionSecret
  let generation := t.generation.toNat
  if !(leafInd < 2^levels) then
    throw (IO.userError "leaf index not in bounds\n")
  else
    let leafTreeSecret ← extractResult (leafKdf encryptionSecret levels 0 leafInd)

    let handshakeInitRatchet ← extractResult (initHandshakeRatchet leafTreeSecret)
    let applicationInitRatchet ← extractResult (initApplicationRatchet leafTreeSecret)
    let handshakeKeyNonce ← extractResult (ratchetGetGenerationKey handshakeInitRatchet generation)
    let applicationKeyNonce ← extractResult (ratchetGetGenerationKey applicationInitRatchet generation)

    checkEqual "handshake_key" bytesToHexString (← hexStringToBytes t.handshakeKey) handshakeKeyNonce.key
    checkEqual "handshake_nonce" bytesToHexString (← hexStringToBytes t.handshakeNonce) handshakeKeyNonce.nonce
    checkEqual "application_key" bytesToHexString (← hexStringToBytes t.applicationKey) applicationKeyNonce.key
    checkEqual "application_nonce" bytesToHexString (← hexStringToBytes t.applicationNonce) applicationKeyNonce.nonce

/-- Port of `test_leaves_aux`. -/
public
def testLeavesAux (levels: Nat) (leafIndex: Nat) (encryptionSecret: String): List SecretTreeLeaf → IO Unit
  | [] => pure ()
  | h::t => do
    testLeaf levels leafIndex encryptionSecret h
    testLeavesAux levels leafIndex encryptionSecret t

/-- Port of `test_leaves`. -/
public
def testLeaves (levels: Nat) (leafIndex: Nat) (encryptionSecret: String): List (List SecretTreeLeaf) → IO Unit
  | [] => pure ()
  | h::t => do
    testLeavesAux levels leafIndex encryptionSecret h
    testLeaves levels (leafIndex+1) encryptionSecret t

end CryptoBytes

/-- Port of `test_secret_tree_one`. -/
public
def testSecretTreeOne (t: SecretTreeTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    testSenderData t.senderData
    let nLeaves := t.leaves.length
    let levels := if nLeaves = 0 then 0 else log2 nLeaves
    testLeaves levels 0 t.encryptionSecret t.leaves
    pure true

/-- Port of `test_secret_tree`. -/
public
def testSecretTree: List SecretTreeTest → IO Nat :=
  testList "Secret Tree" testSecretTreeOne

end MLS.Test.FromExt.SecretTree
