module

public import MLS.Common.Code.Crypto.Derived
public import MLS.TreeDEM.Code.Keys
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.CryptoBasics`.
-/

namespace MLS.Test.FromExt.CryptoBasics

open Comparse
open MLS MLS.TreeDEM
open MLS.Test

variable [CryptoBytes ByteArray]

@[expose]
public
def checkLabel (label: String): IO Unit :=
  if decide (isAsciiString label) && label.length < 2^30 - 8 then
    pure ()
  else
    throw (IO.userError "Error: malformed label")

/-- Port of `test_ref_hash`. -/
@[expose]
public
def testRefHash (t: CryptoBasicsRefHash): IO Unit := do
  checkLabel t.label
  let value ← hexStringToBytes t.value
  let out ← extractResult (refHash t.label value)
  checkEqual "ref hash" bytesToHexString (← hexStringToBytes t.out) out

/-- Port of `test_expand_with_label`. -/
@[expose]
public
def testExpandWithLabel (t: CryptoBasicsExpandWithLabel): IO Unit := do
  checkLabel t.label
  let secret ← hexStringToBytes t.secret
  let context ← hexStringToBytes t.context
  let out ← extractResult (expandWithLabel secret t.label context t.length.toNat)
  checkEqual "expand with label" bytesToHexString (← hexStringToBytes t.out) out

/-- Port of `test_derive_secret`. -/
@[expose]
public
def testDeriveSecret (t: CryptoBasicsDeriveSecret): IO Unit := do
  checkLabel t.label
  let secret ← hexStringToBytes t.secret
  let out ← extractResult (deriveSecret secret t.label)
  checkEqual "derive secret" bytesToHexString (← hexStringToBytes t.out) out

/-- Port of `test_derive_tree_secret`. -/
@[expose]
public
def testDeriveTreeSecret (t: CryptoBasicsDeriveTreeSecret): IO Unit := do
  checkLabel t.label
  let secret ← hexStringToBytes t.secret
  let out ← extractResult (deriveTreeSecret secret t.label t.generation.toNat t.length.toNat)
  checkEqual "derive tree secret" bytesToHexString (← hexStringToBytes t.out) out

/-- Port of `test_sign_with_label`. -/
@[expose]
public
def testSignWithLabel (t: CryptoBasicsSignWithLabel): IO Unit := do
  let priv ← hexStringToBytes t.priv
  let pub ← hexStringToBytes t.pub
  let content ← hexStringToBytes t.content
  let signature ← hexStringToBytes t.signature
  checkLabel t.label
  let signatureOk := verifyWithLabel pub t.label content signature
  let (_, nonce) := genRandBytes (initRandState 0xC0FFEE) (CryptoBytes.signSignMinEntropyLength ByteArray)
  let mySignature ← extractResult (signWithLabel priv t.label content nonce)
  let signatureRoundtripOk := verifyWithLabel pub t.label content mySignature
  if !signatureOk then
    throw (IO.userError "test_sign_with_label: wrong signature")
  if !signatureRoundtripOk then
    throw (IO.userError "test_sign_with_label: wrong signature roundtrip")

/-- Port of `test_encrypt_with_label`. -/
@[expose]
public
def testEncryptWithLabel (t: CryptoBasicsEncryptWithLabel): IO Unit := do
  let priv ← hexStringToBytes t.priv
  let pub ← hexStringToBytes t.pub
  let context ← hexStringToBytes t.context
  let plaintext ← hexStringToBytes t.plaintext
  let kemOutput ← hexStringToBytes t.kemOutput
  let ciphertext ← hexStringToBytes t.ciphertext
  checkLabel t.label
  let myPlaintext ← extractResult (decryptWithLabel priv t.label context kemOutput ciphertext)
  let (_, nonce) := genRandBytes (initRandState 0xC0FFEE) (CryptoBytes.hpkePrivateKeyLength ByteArray)
  let (kemOutput, ciphertext) ← extractResult (encryptWithLabel pub t.label context plaintext nonce)
  let myPlaintextRoundtrip ← extractResult (decryptWithLabel priv t.label context kemOutput ciphertext)
  checkEqual "encrypt with label plaintext" bytesToHexString plaintext myPlaintext
  checkEqual "encrypt with label plaintext" bytesToHexString plaintext myPlaintextRoundtrip

end MLS.Test.FromExt.CryptoBasics

namespace MLS.Test.FromExt.CryptoBasics

open MLS MLS.Test

/-- Port of `test_crypto_basics_one`. -/
@[expose]
public
def testCryptoBasicsOne (t: CryptoBasicsTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    testRefHash t.refHash
    testExpandWithLabel t.expandWithLabel
    testDeriveSecret t.deriveSecret
    testDeriveTreeSecret t.deriveTreeSecret
    testSignWithLabel t.signWithLabel
    testEncryptWithLabel t.encryptWithLabel
    pure true

/-- Port of `test_crypto_basics`. -/
@[expose]
public
def testCryptoBasics: List CryptoBasicsTest → IO Nat :=
  testList "Crypto Basics" testCryptoBasicsOne

end MLS.Test.FromExt.CryptoBasics
