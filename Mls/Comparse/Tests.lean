import Mls.Comparse.Bytes
import Mls.Comparse.Derived

/-!
Port of `Comparse.Tests.TacticOutput` (the tests on big-endian and QUIC integers).

Port-specific differences:
- The concrete bytes are `ByteArray` (`seq_u8_bytes_like` in Comparse (F*)).
- Tests are run at compile time with `#guard`, instead of the `test` attribute and the metaprogram listing them.
- `ps_nat_lbytes sz` is `bitVecBE sz` (or `uint8`, `uint16BE`, `uint32BE`, `uint64BE`).
- `ps_tls_nat` (minimal-width integers) is not ported:
  its tests are translated to the corresponding fixed-width integer,
  and the `*_low_boundary` tests (specific to `ps_tls_nat`) are dropped.
- The tests on generated sum types and enumerations are not ported.
-/

namespace Comparse.Tests

open Comparse

attribute [local instance] bytesLikeByteArray

/-! ## Utility functions, from MLS* -/

def hexCharToHexDigit (c: Char): Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

-- We do recursion on lists, because recursing on a string is slow
/-- Port of `hex_list_char_to_list_u8`. -/
def hexListCharToListU8: List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | h1::h2::t => do
    let d1 ← hexCharToHexDigit h1
    let d2 ← hexCharToHexDigit h2
    let bs ← hexListCharToListU8 t
    some ((16*d1 + d2).toUInt8::bs)

/-- Port of `hex_string_to_bytes`. -/
def hexStringToBytes (s: String): Option ByteArray :=
  (hexListCharToListU8 s.toList).map (fun l => ⟨l.toArray⟩)

/-- Port of `hex_digit_to_hex_string`. -/
def hexDigitToHexString (n: Nat): String :=
  String.singleton (if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10))

/-- Port of `nat_to_hex_string_aux`. -/
def natToHexStringAux (n: Nat): String :=
  if n = 0 then ""
  else natToHexStringAux (n/16) ++ hexDigitToHexString (n%16)

/-- Port of `nat_to_hex_string`. -/
def natToHexString (n: Nat): String :=
  if n = 0 then "00"
  else
    let res := natToHexStringAux n
    if res.length % 2 = 1 then
      "0" ++ res
    else
      res

/-! ## Unit tests -/

/-- Port of `parse_ok`. -/
def parseOk {a: Type} [BEq a] (mf: NonExtensibleMessageFormat ByteArray a) (s: String) (x: a): Bool :=
  match hexStringToBytes s with
  | none => false
  | some b => mf.toExtensible.parse b == some x

/-- Port of `parse_fail`. -/
def parseFail {a: Type} (mf: NonExtensibleMessageFormat ByteArray a) (s: String): Bool :=
  match hexStringToBytes s with
  | none => false
  | some b => (mf.toExtensible.parse b).isNone

/-- Serialization is the inverse of parsing, on the given test vector. -/
def serializeOk {a: Type} (mf: NonExtensibleMessageFormat ByteArray a) (s: String) (x: a): Bool :=
  hexStringToBytes s == some (mf.toExtensible.serialize x)

instance: BEq QuicNat where
  beq x y := x.val == y.val

-- ps_nat_lbytes_is_big_endian
#guard parseOk (NonExtensibleMessageFormat.bitVecBE 8) "0123456789ABCDEF" 0x0123456789ABCDEF
#guard parseOk .uint64BE "0123456789ABCDEF" 0x0123456789ABCDEF
#guard serializeOk .uint64BE "0123456789ABCDEF" 0x0123456789ABCDEF

-- ps_tls_nat_1_low
#guard parseOk .uint8 "00" 0
-- ps_tls_nat_1_high
#guard parseOk .uint8 "FF" (2^8-1)

-- ps_tls_nat_2_low
#guard parseOk .uint16BE "0000" 0
-- ps_tls_nat_2_high
#guard parseOk .uint16BE "FFFF" (2^16-1)

-- ps_tls_nat_3_low
#guard parseOk (NonExtensibleMessageFormat.bitVecBE 3) "000000" 0
-- ps_tls_nat_3_high
#guard parseOk (NonExtensibleMessageFormat.bitVecBE 3) "FFFFFF" (2^24-1)

-- ps_tls_nat_4_low
#guard parseOk .uint32BE "00000000" 0
-- ps_tls_nat_4_high
#guard parseOk .uint32BE "FFFFFFFF" (2^32-1)

/-- Port of `mk_quic_nat`. -/
def mkQuicNat (sz: Nat) (n: Nat): String :=
  natToHexString (sz * 2^(8*(2^sz)-2) + n)

def quicNatOk (sz: Nat) (n: Nat): Bool :=
  if h: n < 2^62 then
    parseOk .quicNat (mkQuicNat sz n) ⟨n, h⟩ && serializeOk .quicNat (mkQuicNat sz n) ⟨n, h⟩
  else
    false

-- ps_quic_nat_1_low_ok
#guard quicNatOk 0 0
-- ps_quic_nat_1_high_ok
#guard quicNatOk 0 (2^(1*8-2)-1)
-- ps_quic_nat_2_fail
#guard parseFail .quicNat (mkQuicNat 1 (2^(1*8-2)-1))
-- ps_quic_nat_2_low_ok
#guard quicNatOk 1 (2^(1*8-2))
-- ps_quic_nat_2_high_ok
#guard quicNatOk 1 (2^(2*8-2)-1)
-- ps_quic_nat_4_fail
#guard parseFail .quicNat (mkQuicNat 2 (2^(2*8-2)-1))
-- ps_quic_nat_4_low_ok
#guard quicNatOk 2 (2^(2*8-2))
-- ps_quic_nat_4_high_ok
#guard quicNatOk 2 (2^(4*8-2)-1)
-- ps_quic_nat_8_fail
#guard parseFail .quicNat (mkQuicNat 3 (2^(4*8-2)-1))
-- ps_quic_nat_8_low_ok
#guard quicNatOk 3 (2^(4*8-2))
-- ps_quic_nat_8_high_ok
#guard quicNatOk 3 (2^(8*8-2)-1)

structure SimpleRecord where
  simpleRecord1: UInt8
  simpleRecord2: UInt16
  simpleRecord3: BitVec (8*3)
  simpleRecord4: UInt32
deriving BEq

def SimpleRecord.f: UInt8 × UInt16 × BitVec (8*3) × UInt32 → SimpleRecord :=
  fun (simpleRecord1, simpleRecord2, simpleRecord3, simpleRecord4) =>
    { simpleRecord1, simpleRecord2, simpleRecord3, simpleRecord4 }

def SimpleRecord.g: SimpleRecord → UInt8 × UInt16 × BitVec (8*3) × UInt32 :=
  fun { simpleRecord1, simpleRecord2, simpleRecord3, simpleRecord4 } =>
    (simpleRecord1, simpleRecord2, simpleRecord3, simpleRecord4)

def SimpleRecord.mf: NonExtensibleMessageFormat ByteArray SimpleRecord :=
  .isomorphic (.prod .uint8 (.prod .uint16BE (.prod (.bitVecBE 3) .uint32BE))) SimpleRecord.f SimpleRecord.g

-- ps_simple_record_ok
#guard parseOk SimpleRecord.mf "11222233333344444444"
  {
    simpleRecord1 := 0x11
    simpleRecord2 := 0x2222
    simpleRecord3 := 0x333333
    simpleRecord4 := 0x44444444
  }

end Comparse.Tests
