module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Common.Proofs.Crypto.Derived
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.Hash

/-!
Lemmas on symbolic bytes that DY* proves by normalization (DY*'s `normalize_term_spec`):
symbolic bytes are terms, so their constructors are injective and have disjoint images.

Port-specific differences:
- DyLean's bytes functor is abstract: bytes built by different constructors are distinguished
  by their usages or labels under the bytes invariants (e.g. `literalToBytes_ne_kdfExtract`).

It also contains the weakenings of the well-formedness of messages (Comparse's `wf_weaken_lemma`)
used by the invariants of states (`wf_publishable_later`, `wf_invariant_later`, `wf_knowableBy_of_publishable`, `wf_knowableBy_canFlow`),
proved on the serialized message (`pred_serializeNE_iff`), as DyLean does.
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

/-- The symbolic hash has length `hashOutputLength` (MLS*'s `hash_output_length_lemma`). -/
public
theorem hashHash_length (buf h: Bytes) (hh: CryptoBytes.hashHash buf = .success h):
  Comparse.BytesLike.length h = CryptoBytes.hashOutputLength Bytes
:= by
  simp only [CryptoBytes.hashHash, Result.pure_eq_success] at hh
  subst hh
  simp [Comparse.BytesLike.length, DY.Hash.length_hash, DY.Hash.hashLength, CryptoBytes.hashOutputLength]

end Injectivity

section Disjointness

variable [HasSymbolicInvariants]

/-- A literal is not the result of `kdfExtract` (their usages differ). -/
public
theorem literalToBytes_ne_kdfExtract (lit: ByteArray) (salt ikm: Bytes):
  DY.Literal.literalToBytes lit ≠ DySlop.KdfExtract.kdfExtract salt ikm
:= by
  intro heq
  have := congrArg (fun b: Bytes => b.usage Trace.empty) heq
  simp [DY.Literal.literalToBytes, Bytes.usage.eq, DY.Literal.Literal.invariants, DySlop.KdfExtract.extractedKeyUsage,
    Usage.nothing, Usage.kdfExpandKey] at this

end Disjointness

section WellFormed

open Comparse

variable [HasSymbolicInvariants]

/-- Publishable messages stay publishable when the trace grows (MLS* uses `wf_weaken_lemma`). -/
public
theorem wf_publishable_later {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (tr1 tr2: ProofTrace) (x: α)
  : tr1 ≤ tr2 →
    mf.wf (Bytes.Publishable · tr1) x →
    mf.wf (Bytes.Publishable · tr2) x
:= by
  rw [← pred_serializeNE_iff, ← pred_serializeNE_iff]
  grind

grind_pattern wf_publishable_later => tr1 ≤ tr2, mf.wf (Bytes.Publishable · tr1) x
grind_pattern [grind_later] wf_publishable_later => tr1 ≤ tr2, mf.wf (Bytes.Publishable · tr1) x

/-- Messages satisfying the bytes invariant still do when the trace grows (MLS* uses `wf_weaken_lemma`). -/
public
theorem wf_invariant_later {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (tr1 tr2: ProofTrace) (x: α)
  : tr1 ≤ tr2 →
    mf.wf (Bytes.Invariant · tr1) x →
    mf.wf (Bytes.Invariant · tr2) x
:= by
  rw [← pred_serializeNE_iff, ← pred_serializeNE_iff]
  grind

grind_pattern wf_invariant_later => tr1 ≤ tr2, mf.wf (Bytes.Invariant · tr1) x
grind_pattern [grind_later] wf_invariant_later => tr1 ≤ tr2, mf.wf (Bytes.Invariant · tr1) x

/-- Publishable messages are knowable by any label (MLS* uses `wf_weaken_lemma`). -/
public
theorem wf_knowableBy_of_publishable {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (l: Label) (tr: ProofTrace) (x: α)
  : mf.wf (Bytes.Publishable · tr) x →
    mf.wf (Bytes.KnowableBy l · tr) x
:= by
  rw [← pred_serializeNE_iff, ← pred_serializeNE_iff]
  grind [canFlowTrans]

/-- Publishable messages satisfy the bytes invariant (MLS* uses `wf_weaken_lemma`). -/
public
theorem wf_invariant_of_publishable {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (tr: ProofTrace) (x: α)
  : mf.wf (Bytes.Publishable · tr) x →
    mf.wf (Bytes.Invariant · tr) x
:= by
  rw [← pred_serializeNE_iff, ← pred_serializeNE_iff]
  grind

/-- Messages knowable by a label are knowable by the labels it flows to (MLS* uses `is_well_formed_prefix_weaken`). -/
public
theorem wf_knowableBy_canFlow {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (l1 l2: Label) (tr: ProofTrace) (x: α)
  : l1.canFlow l2 tr.erase →
    mf.wf (Bytes.KnowableBy l1 · tr) x →
    mf.wf (Bytes.KnowableBy l2 · tr) x
:= by
  rw [← pred_serializeNE_iff, ← pred_serializeNE_iff]
  grind [canFlowTrans]

end WellFormed

end MLS
