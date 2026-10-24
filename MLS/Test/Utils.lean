import Lean.Data.Json
import MLS.Comparse.Bytes
import MLS.Common.Code.Result

/-!
Port of `MLS.Test.Utils` (the parts needed by the ported tests).

Port-specific differences:
- The concrete bytes are `ByteArray` (instead of HACL*'s bytes),
  with the proven `BytesLike` instance of `MLS.Comparse.Bytes`.
- `ML` effects (`failwith`) are translated to `IO` exceptions.
-/

open Comparse

namespace MLS.Test

/-! ## Test harness -/

/-- Port of `check_equal`. -/
def checkEqual {a: Type} [BEq a] (name: String) (toStr: a → String) (x y: a): IO Unit :=
  if x != y then
    throw (IO.userError s!"check_equal {name}: expected '{toStr x}', got '{toStr y}'")
  else
    pure ()

/-- Port of `add_exn_context`. -/
def addExnContext {a: Type} (context: String) (f: Unit → IO a): IO a :=
  tryCatch (f ()) (fun ex => throw (IO.userError s!"{context}\n{ex}"))

/-- Port of `test_list_aux`. -/
def testListAux {a: Type} (testName: String) (test: a → IO Bool): Nat → List a → IO Nat
  | _, [] => pure 0
  | n, h::t => do
    let b ← addExnContext s!"{testName}: failed test {n}" (fun () => test h)
    let rest ← testListAux testName test (n+1) t
    pure ((if b then 1 else 0) + rest)

/-- Port of `test_list`. -/
def testList {a: Type} (testName: String) (test: a → IO Bool) (l: List a): IO Nat :=
  testListAux testName test 0 l

/-! ## Results -/

/-- Port of `extract_result`. -/
def extractResult {α: Type} (x: MLS.Result α): IO α :=
  match x with
  | .success x => pure x
  | .internalError s => throw (IO.userError s!"InternalError: {s}")
  | .protocolError s => throw (IO.userError s!"ProtocolError: {s}")

/-! ## Deterministic randomness -/

structure RandState where
  internalState: Nat

/-- Port of `init_rand_state`. -/
def initRandState (seed: Nat): RandState :=
  { internalState := seed % 2^64 }

/-- Port of `gen_rand_bits`. -/
def genRandBits (st: RandState) (nBits: Nat): RandState × Nat :=
  let res := (6364136223846793005 * st.internalState + 1442695040888963407) % 2^64
  ({ internalState := res }, res / 2^(64 - nBits))

/-- Port of `gen_rand_bytes`. -/
def genRandBytes (rng: RandState): Nat → RandState × ByteArray
  | 0 => (rng, .empty)
  | size+1 =>
    let (rng, head) := genRandBits rng 8
    let (rng, tail) := genRandBytes rng size
    (rng, ⟨#[head.toUInt8]⟩ ++ tail)

/-! ## Hexadecimal strings -/

def hexCharToHexDigit (c: Char): IO UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10).toUInt8
  else throw (IO.userError "string_to_hex_digit: digit is not in [0-9A-Fa-f]")

/-- Port of `hex_list_char_to_list_u8`. -/
def hexListCharToListU8: List Char → IO (List UInt8)
  | [] => pure []
  | [_] => throw (IO.userError "string_to_bytes: size is not a multiple of two")
  | h1::h2::t => do
    let d1 ← hexCharToHexDigit h1
    let d2 ← hexCharToHexDigit h2
    let bs ← hexListCharToListU8 t
    pure ((16*d1 + d2)::bs)

/-- Port of `hex_string_to_bytes`. -/
def hexStringToBytes (s: String): IO ByteArray := do
  let l ← hexListCharToListU8 s.toList
  pure ⟨l.toArray⟩

/-- Port of `byte_to_hex_string`. -/
def byteToHexString (x: UInt8): String :=
  let hexDigit (n: Nat): Char := if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
  String.ofList [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)]

/-- Port of `bytes_to_hex_string`. -/
def bytesToHexString (b: ByteArray): String :=
  String.join (b.toList.map byteToHexString)

/-! ## Parsing / serializing -/

/-! As in MLS* (`ps_prefix_to_ps_whole #bytes #bytes_like_bytes`), the `BytesLike` structure is given explicitly. -/

def parse {a: Type} (mf: @NonExtensibleMessageFormat ByteArray bytesLikeByteArray a) (b: ByteArray): Option a :=
  @ExtensibleMessageFormat.parse ByteArray bytesLikeByteArray a (@NonExtensibleMessageFormat.toExtensible ByteArray bytesLikeByteArray a mf) b

def serialize {a: Type} (mf: @NonExtensibleMessageFormat ByteArray bytesLikeByteArray a) (x: a): ByteArray :=
  @ExtensibleMessageFormat.serialize ByteArray bytesLikeByteArray a (@NonExtensibleMessageFormat.toExtensible ByteArray bytesLikeByteArray a mf) x

end MLS.Test
