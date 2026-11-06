module

public import MLS.TreeKEM.Code.PSK
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.PreSharedKeys`.
-/

namespace MLS.Test.FromExt.PreSharedKeys

open Comparse
open MLS MLS.TreeKEM
open MLS.Test

/-- Port of `test_psk_one`. -/
public
def testPskOne (t: PskTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    let pskData ← t.psks.mapM fun psk => do
      let pskId ← extractResult (mkMlsBytes (← hexStringToBytes psk.pskId) "test_psk_one" "psk_id")
      let pskNonce ← extractResult (mkMlsBytes (← hexStringToBytes psk.pskNonce) "test_psk_one" "psk_nonce")
      pure (PreSharedKeyId.external pskId pskNonce, ← hexStringToBytes psk.psk)
    let pskSecret ← extractResult (computePskSecret pskData)
    checkEqual "psk_secret" bytesToHexString (← hexStringToBytes t.pskSecret) pskSecret
    pure true

/-- Port of `test_psk`. -/
public
def testPsk: List PskTest → IO Nat :=
  testList "Pre-Shared Keys" testPskOne

end MLS.Test.FromExt.PreSharedKeys
