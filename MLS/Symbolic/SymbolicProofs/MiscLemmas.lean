module

public import MLS.Symbolic.Code.Symbolic
import all DY.EquationalTheory.Literal

/-!
Lemmas on symbolic bytes that DY* proves by normalization (DY*'s `normalize_term_spec`):
symbolic bytes are terms, so their constructors are injective and have disjoint images.

Port-specific differences:
- DyLean's bytes functor is abstract: bytes built by different constructors are distinguished
  by their usages or labels under the bytes invariants (e.g. `literalToBytes_ne_kdfExtract`).
-/

namespace MLS

open DY

section Injectivity

variable [HasSymbolicBytes]

/-- `kdfExtract` is injective. -/
public
theorem kdfExtract_inj (salt1 ikm1 salt2 ikm2: Bytes):
  DySlop.KdfExtract.kdfExtract salt1 ikm1 = DySlop.KdfExtract.kdfExtract salt2 ikm2 →
    salt1 = salt2 ∧ ikm1 = ikm2
:= by
  simp only [DySlop.KdfExtract.kdfExtract]
  grind

/-- `kdfExpand` is injective. -/
public
theorem kdfExpand_inj (prk1 info1: Bytes) (len1: Nat) (prk2 info2: Bytes) (len2: Nat):
  DySlop.KdfExpand.kdfExpand prk1 info1 len1 = DySlop.KdfExpand.kdfExpand prk2 info2 len2 →
    prk1 = prk2 ∧ info1 = info2 ∧ len1 = len2
:= by
  simp only [DySlop.KdfExpand.kdfExpand]
  grind

/-- `macCompute` is injective. -/
public
theorem macCompute_inj (key1 msg1 key2 msg2: Bytes):
  DySlop.Mac.macCompute key1 msg1 = DySlop.Mac.macCompute key2 msg2 →
    key1 = key2 ∧ msg1 = msg2
:= by
  simp only [DySlop.Mac.macCompute]
  grind

end Injectivity

section Disjointness

variable [HasSymbolicInvariants]

/-- A literal is not the result of `kdfExtract` (their usages differ). -/
public
theorem literalToBytes_ne_kdfExtract (lit: ByteArray) (salt ikm: Bytes):
  DY.Literal.literalToBytes lit ≠ DySlop.KdfExtract.kdfExtract salt ikm
:= by
  intro heq
  have := congrArg (fun b: Bytes => b.usage Trace.nil) heq
  simp [DY.Literal.literalToBytes, Bytes.usage.eq, DY.Literal.Literal.invariants, DySlop.KdfExtract.extractedKeyUsage,
    Usage.nothing, Usage.kdfExpandKey] at this

end Disjointness

end MLS
