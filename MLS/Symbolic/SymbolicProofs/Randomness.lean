module

public import MLS.Symbolic.SymbolicSpec.Randomness
public import MLS.Common.Proofs.Result
public import MLS.Common.Code.Crypto.Derived

/-!
Port of the predicates and lemmas of `MLS.Symbolic.Randomness`:
the usages and labels of the random bytestrings given to the MLS functions.

Port-specific differences:
- MLS*'s randomness is indexed by the lengths of its bytestrings; here, `Randomness Bytes` is a list of bytes,
  and `RandomnessHasGhostData` requires the list of bytestrings and the ghost data to have the same length.
- `generate_randomness_proof` is not ported yet.
-/

namespace MLS

open DY

/-- Port of `randomness_ghost_data`: the usage and label of each random bytestring. -/
public
abbrev RandomnessGhostData [BytesFunctor] [ExecTraceTypes] := List (Usage × Label)

variable [HasSymbolicInvariants]

/-- Port of `randomness_has_ghost_data`. -/
@[expose]
public
def RandomnessHasGhostData (tr: ProofTrace) (rand: Randomness Bytes) (ldata: RandomnessGhostData): Prop :=
  go rand.rand ldata
where
  go: List Bytes → RandomnessGhostData → Prop
  | [], [] => True
  | randCur :: randNext, (usg, lab) :: tdata =>
    randCur.Invariant tr ∧ randCur.HasUsage usg tr ∧ randCur.label tr = lab ∧ go randNext tdata
  | _, _ => False

/-- The first random bytestring has the first usage and label of the ghost data. -/
public
theorem RandomnessHasGhostData.dest (tr: ProofTrace) (rand: Randomness Bytes) (usg: Usage) (lab: Label)
  (ldata: RandomnessGhostData) (randCur: Bytes) (randNext: Randomness Bytes)
  (h: RandomnessHasGhostData tr rand ((usg, lab) :: ldata)) (hdest: destRandomness rand = .success (randCur, randNext)):
  randCur.Invariant tr ∧ randCur.HasUsage usg tr ∧ randCur.label tr = lab ∧ RandomnessHasGhostData tr randNext ldata
:= by
  obtain ⟨_ | _⟩ := rand
  · simp [destRandomness, Result.internalFailure] at hdest
  · simp only [destRandomness, Result.pure_eq_success] at hdest
    grind [RandomnessHasGhostData, RandomnessHasGhostData.go]

/-- Port of `split_randomness_ghost_data_lemma`. -/
public
theorem RandomnessHasGhostData.split (tr: ProofTrace) (l1: List Nat) (rand rand1 rand2: Randomness Bytes)
  (ldata1 ldata2: RandomnessGhostData)
  (h: RandomnessHasGhostData tr rand (ldata1 ++ ldata2)) (hlen: ldata1.length = l1.length)
  (hsplit: splitRandomness l1 rand = .success (rand1, rand2)):
  RandomnessHasGhostData tr rand1 ldata1 ∧ RandomnessHasGhostData tr rand2 ldata2
:= by
  induction l1 generalizing rand rand1 ldata1 with
  | nil =>
    obtain rfl: ldata1 = [] := by grind
    simp only [splitRandomness, Result.pure_eq_success] at hsplit
    grind [RandomnessHasGhostData, RandomnessHasGhostData.go, mkEmptyRandomness]
  | cons _ t1 ih =>
    obtain _ | ⟨⟨usg, lab⟩, tdata⟩ := ldata1
    · exfalso; grind
    simp only [splitRandomness, Result.bind_eq_success, Result.pure_eq_success] at hsplit
    obtain ⟨⟨rh, rt⟩, hdest, ⟨rt1, rl2⟩, hsplit', heq⟩ := hsplit
    obtain ⟨hinv, husg, hlab, hrt⟩ := RandomnessHasGhostData.dest _ _ _ _ _ _ _ h hdest
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨h1, h2⟩ := ih _ _ _ hrt (by simpa using hlen) hsplit'
    exact ⟨⟨hinv, husg, hlab, h1⟩, h2⟩

end MLS
