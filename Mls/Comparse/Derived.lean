import Comparse

/-!
Message formats of Comparse (F*) that are not (yet) available in DyLean's Comparse.

- `NonExtensibleMessageFormat.bitVecBE`, `uint16BE`, `uint32BE`, `uint64BE`: big-endian integers
  (port of `ps_nat_lbytes`; DyLean's `bitVec` and `uintN` are little-endian).
- `NonExtensibleMessageFormat.empty`: the format of `Empty`, which never parses.
  It is used to build tagged unions where some tags are invalid.
- `NonExtensibleMessageFormat.lengthPrefix`: port of `length_prefix_ps_whole`.
- `NonExtensibleMessageFormat.quicNat`: port of `ps_quic_nat`,
  the variable-length integer encoding of QUIC (RFC 9000, Section 16).
-/

namespace Comparse

variable {Bytes: Type} [BytesLike Bytes]

/-! ## Big-endian integers -/

namespace NonExtensibleMessageFormat.bitVecBE

def f0: Unit → BitVec (8*0) := fun _ => 0#0
def g0: BitVec (8*0) → Unit := fun _ => ()

instance: LeftInverse g0 f0 := ⟨by intro _; rfl⟩
instance: RightInverse g0 f0 := ⟨by intro x; exact BitVec.eq_nil x |>.symm⟩

def f (w: Nat): UInt8 × BitVec (8*w) → BitVec (8*(w+1)) :=
  fun (hi, lo) => BitVec.ofNat _ (hi.toNat * 2^(8*w) + lo.toNat)

def g (w: Nat): BitVec (8*(w+1)) → UInt8 × BitVec (8*w) :=
  fun x => (UInt8.ofNat (x.toNat / 2^(8*w)), BitVec.ofNat _ (x.toNat % 2^(8*w)))

theorem lt_aux (w a b: Nat) (ha: a < 256) (hb: b < 2^(8*w)): a * 2^(8*w) + b < 2^(8*(w+1)) := by
  have: 2^(8*(w+1)) = 256 * 2^(8*w) := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
  rw [this]
  have: a * 2^(8*w) + b < (a+1) * 2^(8*w) := by rw [Nat.add_mul]; omega
  have: (a+1) * 2^(8*w) ≤ 256 * 2^(8*w) := Nat.mul_le_mul_right _ ha
  omega

instance (w: Nat): LeftInverse (g w) (f w) := ⟨by
  intro (hi, lo)
  have hhi := hi.toNat_lt
  have hlo := lo.isLt
  have hpos: 0 < 2^(8*w) := Nat.two_pow_pos _
  simp only [f, g, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_aux w _ _ hhi hlo), Prod.mk.injEq]
  constructor
  · apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo]
    simp
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo]⟩

instance (w: Nat): RightInverse (g w) (f w) := ⟨by
  intro x
  have hx := x.isLt
  have hpos: 0 < 2^(8*w) := Nat.two_pow_pos _
  have h2: 2^(8*(w+1)) = 256 * 2^(8*w) := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
  have hx': x.toNat < 2^(8*w) * 256 := by omega
  have hdiv: x.toNat / 2^(8*w) < 256 := Nat.div_lt_of_lt_mul hx'
  apply BitVec.eq_of_toNat_eq
  simp only [f, g, BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hdiv, Nat.mod_mod]
  rw [Nat.div_add_mod' x.toNat]
  exact Nat.mod_eq_of_lt hx⟩

end NonExtensibleMessageFormat.bitVecBE

/--
Big-endian encoding of bit vectors, as `ps_nat_lbytes` in Comparse (F*) with DY*'s `from_nat`.
DyLean's `bitVec` is little-endian, hence cannot be used for MLS.
-/
def NonExtensibleMessageFormat.bitVecBE: (w: Nat) → NonExtensibleMessageFormat Bytes (BitVec (8*w))
  | 0 => isomorphic unit bitVecBE.f0 bitVecBE.g0
  | w+1 => isomorphic (prod uint8 (bitVecBE w)) (bitVecBE.f w) (bitVecBE.g w)

namespace NonExtensibleMessageFormat.bitVecBE

instance instIsNonAmbiguous: ∀ w, (bitVecBE w: NonExtensibleMessageFormat Bytes _).IsNonAmbiguous
  | 0 => by dsimp only [bitVecBE]; infer_instance
  | w+1 => by
    have := instIsNonAmbiguous w
    dsimp only [bitVecBE]; infer_instance

instance instHasUniqueRepresentation: ∀ w, (bitVecBE w: NonExtensibleMessageFormat Bytes _).HasUniqueRepresentation
  | 0 => by dsimp only [bitVecBE]; infer_instance
  | w+1 => by
    have := instHasUniqueRepresentation w
    dsimp only [bitVecBE]; infer_instance

instance (w: Nat): (bitVecBE (w+1): NonExtensibleMessageFormat Bytes _).ParseConsumes := by
  dsimp only [bitVecBE]; infer_instance

end NonExtensibleMessageFormat.bitVecBE

local instance: @LeftInverse UInt16 (BitVec (8*2)) UInt16.toBitVec UInt16.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt16 (BitVec (8*2)) UInt16.toBitVec UInt16.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- Big-endian `uint16`. -/
def NonExtensibleMessageFormat.uint16BE: NonExtensibleMessageFormat Bytes UInt16 :=
  isomorphic (bitVecBE 2) UInt16.ofBitVec UInt16.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

local instance: @LeftInverse UInt32 (BitVec (8*4)) UInt32.toBitVec UInt32.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt32 (BitVec (8*4)) UInt32.toBitVec UInt32.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- Big-endian `uint32`. -/
def NonExtensibleMessageFormat.uint32BE: NonExtensibleMessageFormat Bytes UInt32 :=
  isomorphic (bitVecBE 4) UInt32.ofBitVec UInt32.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

local instance: @LeftInverse UInt64 (BitVec (8*8)) UInt64.toBitVec UInt64.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt64 (BitVec (8*8)) UInt64.toBitVec UInt64.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- Big-endian `uint64`. -/
def NonExtensibleMessageFormat.uint64BE: NonExtensibleMessageFormat Bytes UInt64 :=
  isomorphic (bitVecBE 8) UInt64.ofBitVec UInt64.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

/-! ## Empty -/

def NonExtensibleMessageFormat.empty: NonExtensibleMessageFormat Bytes Empty where
  parse _ := none
  serialize x := nomatch x
  parse_wf := by simp

namespace NonExtensibleMessageFormat.empty

instance: (empty: NonExtensibleMessageFormat Bytes Empty).IsNonAmbiguous where
  parse_serialize_inv x := nomatch x

instance: (empty: NonExtensibleMessageFormat Bytes Empty).HasUniqueRepresentation where
  serialize_parse_inv _ := trivial

instance: (empty: NonExtensibleMessageFormat Bytes Empty).ParseConsumes where
  parse_consumes _ := trivial

end NonExtensibleMessageFormat.empty

/-! ## Length prefix -/

namespace NonExtensibleMessageFormat.lengthPrefix

variable {a: Type} {pre: Nat → Prop} {mf: ExtensibleMessageFormat Bytes a}

abbrev Raw (pre: Nat → Prop) (mf: ExtensibleMessageFormat Bytes a) :=
  (n: {n: Nat // pre n}) × {x: a // BytesLike.length (mf.serialize x) = n.val}

def f (x: Raw pre mf): {x: a // pre (BytesLike.length (mf.serialize x))} :=
  ⟨x.snd.val, by rw [x.snd.property]; exact x.fst.property⟩

def g (x: {x: a // pre (BytesLike.length (mf.serialize x))}): Raw pre mf :=
  ⟨⟨BytesLike.length (mf.serialize x.val), x.property⟩, ⟨x.val, rfl⟩⟩

instance: LeftInverse (g (pre := pre) (mf := mf)) f where
  left_inv := by
    intro ⟨⟨n, hn⟩, ⟨x, hx⟩⟩
    simp only at hx
    subst hx
    rfl

instance: RightInverse (g (pre := pre) (mf := mf)) f where
  right_inv := by
    intro _
    rfl

theorem serialize_length (mf: ExtensibleMessageFormat Bytes a) (n: Nat):
  ∀ x, BytesLike.length ((ExtensibleMessageFormat.subtype mf (fun x => BytesLike.length (mf.serialize x) = n)).serialize x) = n
:=
  fun x => x.property

abbrev payload (mf: ExtensibleMessageFormat Bytes a) (n: Nat) :=
  (ExtensibleMessageFormat.subtype mf (fun x => BytesLike.length (mf.serialize x) = n)).toNonExtensible
    n (serialize_length mf n)

end NonExtensibleMessageFormat.lengthPrefix

/--
Port of `length_prefix_ps_whole`:
serialize `x` with the (extensible) format `mf`, and prefix it with its length.
-/
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

abbrev QuicNat := {n: Nat // n < 2^62}

namespace NonExtensibleMessageFormat.quicNat

/-- The first byte is split into 2 bits (the log of the length) and 6 bits (the most significant bits of the integer). -/
def firstByte.f (x: UInt8): Fin 4 × Fin 64 :=
  (⟨x.toNat / 64, by have := x.toNat_lt; omega⟩, ⟨x.toNat % 64, by omega⟩)

def firstByte.g (x: Fin 4 × Fin 64): UInt8 :=
  UInt8.ofNat (x.1.val * 64 + x.2.val)

instance: LeftInverse firstByte.g firstByte.f where
  left_inv x := by
    have := x.toNat_lt
    apply UInt8.toNat_inj.mp
    simp only [firstByte.f, firstByte.g, UInt8.toNat_ofNat']
    omega

instance: RightInverse firstByte.g firstByte.f where
  right_inv x := by
    obtain ⟨⟨l, hl⟩, ⟨b, hb⟩⟩ := x
    simp only [firstByte.f, firstByte.g, UInt8.toNat_ofNat', Prod.mk.injEq, Fin.mk.injEq]
    omega

def firstByte: NonExtensibleMessageFormat Bytes (Fin 4 × Fin 64) :=
  isomorphic uint8 firstByte.f firstByte.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

/-- Number of bytes following the first byte. -/
def remLen: Fin 4 → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 7

/-- Minimal value that must be encoded with a given length, to ensure unique representation. -/
def minVal: Fin 4 → Nat
  | 0 => 0
  | 1 => 2^6
  | 2 => 2^14
  | 3 => 2^30

def logLen (n: Nat): Fin 4 :=
  if n < 2^6 then 0 else if n < 2^14 then 1 else if n < 2^30 then 2 else 3

theorem logLen_spec (n: Nat) (h: n < 2^62):
  minVal (logLen n) ≤ n ∧ n < 2^(6 + 8 * remLen (logLen n))
:= by
  unfold logLen
  split <;> (try split) <;> (try split) <;> simp [remLen, minVal] <;> omega

theorem logLen_unique (n: Nat) (l: Fin 4) (h1: minVal l ≤ n) (h2: n < 2^(6 + 8 * remLen l)):
  logLen n = l
:= by
  rcases l with ⟨_|_|_|_|l, hl⟩ <;> simp [logLen, remLen, minVal] at * <;> grind

abbrev Raw := (fb: Fin 4 × Fin 64) × BitVec (8 * remLen fb.1)

def f (x: Raw): Option QuicNat :=
  let n := x.1.2.val * 2^(8 * remLen x.1.1) + x.2.toNat
  if h: n < 2^62 ∧ minVal x.1.1 ≤ n then
    some ⟨n, h.1⟩
  else
    none

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
  simp only [g, Sigma.mk.injEq, Prod.mk.injEq, true_and, heq_eq_eq]
  constructor
  · exact Fin.ext hb
  · apply BitVec.eq_of_toNat_eq; simp [← hr]

instance: SubsetRightInverse g f where
  right_inv n := by
    obtain ⟨n, hn⟩ := n
    have := logLen_spec n hn
    simp only [f, g, BitVec.toNat_ofNat]
    have := Nat.div_add_mod' n (2 ^ (8 * remLen (logLen n)))
    simp only [this]
    simp_all

instance: SubsetLeftInverse g f where
  left_inv x := by
    obtain ⟨⟨l, b⟩, r⟩ := x
    simp only [f]
    split
    · trivial
    rename_i y h
    split at h
    · rename_i hn
      cases h
      have hb := b.isLt
      have hr := r.isLt
      have hpow: 2^(6 + 8 * remLen l) = 64 * 2^(8 * remLen l) := by rw [Nat.pow_add]
      apply g_eq
      · apply logLen_unique
        · exact hn.2
        · rw [hpow]
          show b.val * 2^(8 * remLen l) + r.toNat < 64 * 2^(8 * remLen l)
          have hr': r.toNat < 2^(8 * remLen l) := hr
          clear hn hpow hr
          generalize 2^(8 * remLen l) = k at *
          have: b.val * k + r.toNat < (b.val + 1) * k := by grind
          have: (b.val + 1) * k ≤ 64 * k := Nat.mul_le_mul_right _ hb
          omega
      · simp only
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr]
        simp
      · simp only
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    · contradiction

end NonExtensibleMessageFormat.quicNat

/-- Port of `ps_quic_nat`. -/
def NonExtensibleMessageFormat.quicNat: NonExtensibleMessageFormat Bytes QuicNat :=
  subsetIsomorphic (sigma quicNat.firstByte (fun fb => bitVecBE (quicNat.remLen fb.1))) quicNat.f quicNat.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

end Comparse
