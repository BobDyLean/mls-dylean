module

public import Comparse
import all Comparse.Formats.Derived

/-!
Message formats of Comparse (F*) that are not (yet) available in DyLean's Comparse.

- `NonExtensibleMessageFormat.bitVecBE`, `uint16BE`, `uint32BE`, `uint64BE`: big-endian integers
  (port of `ps_nat_lbytes`; DyLean's `bitVec` and `uintN` are little-endian).
- `NonExtensibleMessageFormat.empty`: the format of `Empty`, which never parses.
  It is used to build tagged unions where some tags are invalid.
- `NonExtensibleMessageFormat.lengthPrefix`: port of `length_prefix_ps_whole`.
- `NonExtensibleMessageFormat.slowList`: lists prefixed by their length (in `slowNat`),
  the non-extensible format of lists used by the symbolic states (port of Comparse's `ps_list`).
- `NonExtensibleMessageFormat.quicNat`: port of `ps_quic_nat`,
  the variable-length integer encoding of QUIC (RFC 9000, Section 16).
- `ExtensibleMessageFormat.list.serialize_nil`, `serialize_cons`: equations of DyLean's `list`,
  whose definition is not exposed.
-/

namespace Comparse

variable {Bytes: Type} [BytesLike Bytes]

/-! ## Lists -/

namespace ExtensibleMessageFormat.list

@[simp]
public
theorem serialize_nil {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]:
  (ExtensibleMessageFormat.list mf).serialize [] = BytesLike.empty
:= by
  simp only [ExtensibleMessageFormat.list, ExtensibleMessageFormat.list.serialize]

@[simp]
public
theorem serialize_cons {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (h: a) (t: List a):
  (ExtensibleMessageFormat.list mf).serialize (h :: t) =
    concatPrefixes (mf.serialize h) ((ExtensibleMessageFormat.list mf).serialize t)
:= by
  simp only [ExtensibleMessageFormat.list, ExtensibleMessageFormat.list.serialize]

end ExtensibleMessageFormat.list

/-! ## Big-endian integers -/

namespace NonExtensibleMessageFormat.bitVecBE

@[expose]
public
def f0: Unit → BitVec (8*0) := fun _ => 0#0
@[expose]
public
def g0: BitVec (8*0) → Unit := fun _ => ()

public
instance: LeftInverse g0 f0 := ⟨by intro _; rfl⟩
public
instance: RightInverse g0 f0 := ⟨by intro x; exact BitVec.eq_nil x |>.symm⟩

@[expose]
public
def f (w: Nat): UInt8 × BitVec (8*w) → BitVec (8*(w+1)) :=
  fun (hi, lo) => BitVec.ofNat _ (hi.toNat * 2^(8*w) + lo.toNat)

@[expose]
public
def g (w: Nat): BitVec (8*(w+1)) → UInt8 × BitVec (8*w) :=
  fun x => (UInt8.ofNat (x.toNat / 2^(8*w)), BitVec.ofNat _ (x.toNat % 2^(8*w)))

theorem lt_aux (w a b: Nat) (ha: a < 256) (hb: b < 2^(8*w)): a * 2^(8*w) + b < 2^(8*(w+1)) := by
  have := Nat.mul_le_mul_right (2^(8*w)) ha
  grind

public
instance (w: Nat): LeftInverse (g w) (f w) := ⟨by
  intro (hi, lo)
  have hlo := lo.isLt
  simp only [f, g, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_aux w _ _ hi.toNat_lt hlo), Prod.mk.injEq,
    ← UInt8.toNat_inj, BitVec.toNat_eq, UInt8.toNat_ofNat']
  simp [Nat.add_comm _ lo.toNat, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.mod_eq_of_lt hlo]⟩

public
instance (w: Nat): RightInverse (g w) (f w) := ⟨by
  intro x
  have hx := x.isLt
  have hdiv: x.toNat / 2^(8*w) < 256 := Nat.div_lt_of_lt_mul (by grind)
  simp only [f, g, BitVec.toNat_eq, BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hdiv, Nat.mod_mod,
    Nat.div_add_mod', Nat.mod_eq_of_lt hx]⟩

end NonExtensibleMessageFormat.bitVecBE

/--
Big-endian encoding of bit vectors, as `ps_nat_lbytes` in Comparse (F*) with DY*'s `from_nat`.
DyLean's `bitVec` is little-endian, hence cannot be used for MLS.
-/
@[expose]
public
def NonExtensibleMessageFormat.bitVecBE: (w: Nat) → NonExtensibleMessageFormat Bytes (BitVec (8*w))
  | 0 => isomorphic unit bitVecBE.f0 bitVecBE.g0
  | w+1 => isomorphic (prod uint8 (bitVecBE w)) (bitVecBE.f w) (bitVecBE.g w)

namespace NonExtensibleMessageFormat.bitVecBE

public
instance instIsNonAmbiguous: ∀ w, (bitVecBE w: NonExtensibleMessageFormat Bytes _).IsNonAmbiguous
  | 0 => by dsimp only [bitVecBE]; infer_instance
  | w+1 => by
    have := instIsNonAmbiguous w
    dsimp only [bitVecBE]; infer_instance

public
instance instHasUniqueRepresentation: ∀ w, (bitVecBE w: NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation
  | 0 => by dsimp only [bitVecBE]; infer_instance
  | w+1 => by
    have := instHasUniqueRepresentation w
    dsimp only [bitVecBE]; infer_instance

public
instance (w: Nat): (bitVecBE (w+1): NonExtensibleMessageFormat Bytes _).ParseConsumes := by
  dsimp only [bitVecBE]; infer_instance

/-- Big-endian integers contain no bytes (their well-formedness is trivial). -/
@[simp]
public
theorem wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred]: ∀ (w: Nat) (x: BitVec (8*w)),
    (bitVecBE w: NonExtensibleMessageFormat Bytes _).wf pred x = True
  | 0, x => by simp [bitVecBE]
  | w+1, x => by simp [bitVecBE, wf_eq pred w]

end NonExtensibleMessageFormat.bitVecBE

public local instance: @LeftInverse UInt16 (BitVec (8*2)) UInt16.toBitVec UInt16.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

public local instance: @RightInverse UInt16 (BitVec (8*2)) UInt16.toBitVec UInt16.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- Big-endian `uint16`. -/
@[expose]
public
def NonExtensibleMessageFormat.uint16BE: NonExtensibleMessageFormat Bytes UInt16 :=
  isomorphic (bitVecBE 2) UInt16.ofBitVec UInt16.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint16BE.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UInt16):
  (uint16BE: NonExtensibleMessageFormat Bytes UInt16).wf pred x = True
:= by
  simp [uint16BE, bitVecBE]

public local instance: @LeftInverse UInt32 (BitVec (8*4)) UInt32.toBitVec UInt32.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

public local instance: @RightInverse UInt32 (BitVec (8*4)) UInt32.toBitVec UInt32.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- Big-endian `uint32`. -/
@[expose]
public
def NonExtensibleMessageFormat.uint32BE: NonExtensibleMessageFormat Bytes UInt32 :=
  isomorphic (bitVecBE 4) UInt32.ofBitVec UInt32.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint32BE.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UInt32):
  (uint32BE: NonExtensibleMessageFormat Bytes UInt32).wf pred x = True
:= by
  simp only [uint32BE, isomorphic.wf_eq, bitVecBE.wf_eq]

public local instance: @LeftInverse UInt64 (BitVec (8*8)) UInt64.toBitVec UInt64.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

public local instance: @RightInverse UInt64 (BitVec (8*8)) UInt64.toBitVec UInt64.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- Big-endian `uint64`. -/
@[expose]
public
def NonExtensibleMessageFormat.uint64BE: NonExtensibleMessageFormat Bytes UInt64 :=
  isomorphic (bitVecBE 8) UInt64.ofBitVec UInt64.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint64BE.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UInt64):
  (uint64BE: NonExtensibleMessageFormat Bytes UInt64).wf pred x = True
:= by
  simp only [uint64BE, isomorphic.wf_eq, bitVecBE.wf_eq]

/-! ## Empty -/

@[expose]
public
def NonExtensibleMessageFormat.empty: NonExtensibleMessageFormat Bytes Empty where
  parse _ := none
  serialize x := nomatch x
  parse_wf := by simp

namespace NonExtensibleMessageFormat.empty

public
instance: (empty: NonExtensibleMessageFormat Bytes Empty).IsNonAmbiguous where
  parse_serialize_inv x := nomatch x

public
instance: (empty: NonExtensibleMessageFormat Bytes Empty).HasUniqueRepresentation where
  serialize_parse_inv _ := trivial

public
instance: (empty: NonExtensibleMessageFormat Bytes Empty).ParseConsumes where
  parse_consumes _ := trivial

@[simp]
public
theorem wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Empty):
  (empty: NonExtensibleMessageFormat Bytes Empty).wf pred x = True
:=
  nomatch x

end NonExtensibleMessageFormat.empty

/-! ## Length prefix -/

namespace NonExtensibleMessageFormat.lengthPrefix

variable {a: Type} {pre: Nat → Prop} {mf: ExtensibleMessageFormat Bytes a}

public
abbrev Raw (pre: Nat → Prop) (mf: ExtensibleMessageFormat Bytes a) :=
  (n: {n: Nat // pre n}) × {x: a // BytesLike.length (mf.serialize x) = n.val}

@[expose]
public
def f (x: Raw pre mf): {x: a // pre (BytesLike.length (mf.serialize x))} :=
  ⟨x.snd.val, by rw [x.snd.property]; exact x.fst.property⟩

@[expose]
public
def g (x: {x: a // pre (BytesLike.length (mf.serialize x))}): Raw pre mf :=
  ⟨⟨BytesLike.length (mf.serialize x.val), x.property⟩, ⟨x.val, rfl⟩⟩

public
instance: LeftInverse (g (pre := pre) (mf := mf)) f where
  left_inv := by
    intro ⟨⟨n, hn⟩, ⟨x, hx⟩⟩
    simp only at hx
    subst hx
    rfl

public
instance: RightInverse (g (pre := pre) (mf := mf)) f where
  right_inv := by
    intro _
    rfl

public
theorem serialize_length (mf: ExtensibleMessageFormat Bytes a) (n: Nat):
  ∀ x, BytesLike.length ((ExtensibleMessageFormat.subtype mf (fun x => BytesLike.length (mf.serialize x) = n)).serialize x) = n
:=
  fun x => x.property

public
abbrev payload (mf: ExtensibleMessageFormat Bytes a) (n: Nat) :=
  (ExtensibleMessageFormat.subtype mf (fun x => BytesLike.length (mf.serialize x) = n)).toNonExtensible
    n (serialize_length mf n)

end NonExtensibleMessageFormat.lengthPrefix

/--
Port of `length_prefix_ps_whole`:
serialize `x` with the (extensible) format `mf`, and prefix it with its length.
-/
@[expose]
public
def NonExtensibleMessageFormat.lengthPrefix
  {a: Type}
  (pre: Nat → Prop)
  (mfLen: NonExtensibleMessageFormat Bytes {n: Nat // pre n})
  (mf: ExtensibleMessageFormat Bytes a)
  : NonExtensibleMessageFormat Bytes {x: a // pre (BytesLike.length (mf.serialize x))}
:=
  isomorphic
    (sigma mfLen (fun n => lengthPrefix.payload mf n.val))
    lengthPrefix.f lengthPrefix.g

namespace NonExtensibleMessageFormat.lengthPrefix

@[simp]
public
theorem wf_eq
  {a: Type} (pre: Nat → Prop) (mfLen: NonExtensibleMessageFormat Bytes {n: Nat // pre n}) (mf: ExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: {x: a // pre (BytesLike.length (mf.serialize x))})
  : (lengthPrefix pre mfLen mf).wf pred x = (mfLen.wf pred ⟨_, x.property⟩ ∧ mf.wf pred x.val)
:= by
  simp [lengthPrefix, g]

public
instance
  {a: Type}
  (pre: Nat → Prop)
  (mfLen: NonExtensibleMessageFormat Bytes {n: Nat // pre n})
  (mf: ExtensibleMessageFormat Bytes a)
  [mfLen.IsNonAmbiguous] [mf.IsNonAmbiguous]
  : (lengthPrefix pre mfLen mf).IsNonAmbiguous
:= by
  dsimp only [lengthPrefix]
  infer_instance

public
instance
  {a: Type}
  (pre: Nat → Prop)
  (mfLen: NonExtensibleMessageFormat Bytes {n: Nat // pre n})
  (mf: ExtensibleMessageFormat Bytes a)
  [mfLen.HasUniqueRepresentation] [mf.HasUniqueRepresentation]
  : (lengthPrefix pre mfLen mf).HasUniqueRepresentation
:= by
  dsimp only [lengthPrefix]
  infer_instance

public
instance
  {a: Type}
  (pre: Nat → Prop)
  (mfLen: NonExtensibleMessageFormat Bytes {n: Nat // pre n})
  (mf: ExtensibleMessageFormat Bytes a)
  [mfLen.ParseConsumes]
  : (lengthPrefix pre mfLen mf).ParseConsumes
:= by
  dsimp only [lengthPrefix]
  infer_instance

end NonExtensibleMessageFormat.lengthPrefix

/-! ## QUIC variable-length integers -/

public
abbrev QuicNat := {n: Nat // n < 2^62}

namespace NonExtensibleMessageFormat.quicNat

/-- The first byte is split into 2 bits (the log of the length) and 6 bits (the most significant bits of the integer). -/
@[expose]
public
def firstByte.f (x: UInt8): Fin 4 × Fin 64 :=
  (⟨x.toNat / 64, by grind⟩, ⟨x.toNat % 64, by grind⟩)

@[expose]
public
def firstByte.g (x: Fin 4 × Fin 64): UInt8 :=
  UInt8.ofNat (x.1.val * 64 + x.2.val)

public
instance: LeftInverse firstByte.g firstByte.f where
  left_inv x := by
    simp only [firstByte.f, firstByte.g, ← UInt8.toNat_inj, UInt8.toNat_ofNat']
    grind

public
instance: RightInverse firstByte.g firstByte.f where
  right_inv x := by
    simp only [firstByte.f, firstByte.g, UInt8.toNat_ofNat', Prod.ext_iff, Fin.ext_iff]
    grind

@[expose]
public
def firstByte: NonExtensibleMessageFormat Bytes (Fin 4 × Fin 64) :=
  isomorphic uint8 firstByte.f firstByte.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

/-- Number of bytes following the first byte. -/
@[expose]
public
def remLen: Fin 4 → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 7

/-- Minimal value that must be encoded with a given length, to ensure unique representation. -/
@[expose]
public
def minVal: Fin 4 → Nat
  | 0 => 0
  | 1 => 2^6
  | 2 => 2^14
  | 3 => 2^30

@[expose]
public
def logLen (n: Nat): Fin 4 :=
  if n < 2^6 then 0 else if n < 2^14 then 1 else if n < 2^30 then 2 else 3

theorem logLen_spec (n: Nat) (h: n < 2^62):
  minVal (logLen n) ≤ n ∧ n < 2^(6 + 8 * remLen (logLen n))
:= by
  grind [logLen, remLen, minVal]

theorem logLen_unique (n: Nat) (l: Fin 4) (h1: minVal l ≤ n) (h2: n < 2^(6 + 8 * remLen l)):
  logLen n = l
:= by
  rcases l with ⟨_|_|_|_|l, hl⟩ <;> simp [logLen, remLen, minVal] at * <;> grind

public
abbrev Raw := (fb: Fin 4 × Fin 64) × BitVec (8 * remLen fb.1)

@[expose]
public
def f (x: Raw): Option QuicNat :=
  let n := x.1.2.val * 2^(8 * remLen x.1.1) + x.2.toNat
  if h: n < 2^62 ∧ minVal x.1.1 ≤ n then
    some ⟨n, h.1⟩
  else
    none

@[expose]
public
def g (n: QuicNat): Raw :=
  ⟨(logLen n.val, ⟨n.val / 2^(8 * remLen (logLen n.val)), by
    have := logLen_spec n.val n.property
    rw [Nat.pow_add] at this
    exact Nat.div_lt_of_lt_mul (by grind)⟩),
   BitVec.ofNat _ n.val⟩

theorem g_eq (n: QuicNat) (l: Fin 4) (b: Fin 64) (r: BitVec (8 * remLen l))
  (hl: logLen n.val = l) (hb: n.val / 2^(8 * remLen l) = b.val) (hr: n.val % 2^(8 * remLen l) = r.toNat):
  g n = ⟨(l, b), r⟩
:= by
  subst hl
  simp [g, Fin.ext_iff, BitVec.toNat_eq, ← hb, ← hr]

public
instance: SubsetRightInverse g f where
  right_inv n := by
    obtain ⟨n, hn⟩ := n
    have := logLen_spec n hn
    simp_all [f, g, Nat.div_add_mod']

public
instance: SubsetLeftInverse g f where
  left_inv x := by
    obtain ⟨⟨l, b⟩, r⟩ := x
    simp only [f]
    split
    · trivial
    rename_i h
    split at h
    · rename_i hn
      cases h
      have hb := b.isLt
      have hr := r.isLt
      apply g_eq
      · apply logLen_unique _ _ hn.2
        have := Nat.mul_le_mul_right (2^(8 * remLen l)) hb
        grind
      · simp [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr]
      · simp [Nat.add_comm, Nat.mod_eq_of_lt hr]
    · contradiction

end NonExtensibleMessageFormat.quicNat

/-- Port of `ps_quic_nat`. -/
@[expose]
public
def NonExtensibleMessageFormat.quicNat: NonExtensibleMessageFormat Bytes QuicNat :=
  subsetIsomorphic (sigma quicNat.firstByte (fun fb => bitVecBE (quicNat.remLen fb.1))) quicNat.f quicNat.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

/-- QUIC integers contain no bytes (their well-formedness is trivial). -/
@[simp]
public
theorem NonExtensibleMessageFormat.quicNat.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: QuicNat):
  (quicNat: NonExtensibleMessageFormat Bytes QuicNat).wf pred x = True
:= by
  simp [quicNat, quicNat.firstByte]

/-! ## Length-prefixed lists -/

namespace NonExtensibleMessageFormat.slowList

@[expose]
public
def lenF (n: Nat): {_n: Nat // True} := ⟨n, trivial⟩

@[expose]
public
def lenG (n: {_n: Nat // True}): Nat := n.val

public
instance: LeftInverse lenG lenF := ⟨by intro _; rfl⟩
public
instance: RightInverse lenG lenF := ⟨by intro _; rfl⟩

/-- The length of the list, in unary (`slowNat`). -/
@[expose]
public
def lenMf: NonExtensibleMessageFormat Bytes {_n: Nat // True} :=
  isomorphic slowNat lenF lenG
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

variable {a: Type} {mf: NonExtensibleMessageFormat Bytes a} [mf.ParseConsumes]

@[expose]
public
def f (x: {l: List a // (fun _ => True) (BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l))}): List a :=
  x.val

@[expose]
public
def g (l: List a): {l: List a // (fun _ => True) (BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l))} :=
  ⟨l, trivial⟩

public
instance: LeftInverse (g (mf := mf)) (f (mf := mf)) := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (mf := mf)) (f (mf := mf)) := ⟨by intro _; rfl⟩

end NonExtensibleMessageFormat.slowList

/--
Lists prefixed by their length (in bytes, encoded with `slowNat`),
the non-extensible format of lists used by the symbolic states (port of Comparse's `ps_list`).
-/
@[expose]
public
def NonExtensibleMessageFormat.slowList {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]:
  NonExtensibleMessageFormat Bytes (List a)
:=
  isomorphic (lengthPrefix (fun _ => True) slowList.lenMf (.list mf)) (slowList.f (mf := mf)) (slowList.g (mf := mf))

namespace NonExtensibleMessageFormat.slowList

public
instance {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] [mf.IsNonAmbiguous]:
  (slowList mf).IsNonAmbiguous
:= by
  dsimp only [slowList]
  infer_instance

public
instance {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] [mf.HasUniqueRepresentation]:
  (slowList mf).HasUniqueRepresentation
:= by
  dsimp only [slowList]
  infer_instance

public
instance {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]:
  (slowList mf).ParseConsumes
:= by
  dsimp only [slowList]
  infer_instance

@[simp]
public
theorem wf_eq {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes]
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: List a):
  (slowList mf).wf pred x = ∀ y ∈ x, mf.wf pred y
:= by
  simp [slowList, g, lenMf]

end NonExtensibleMessageFormat.slowList

end Comparse
