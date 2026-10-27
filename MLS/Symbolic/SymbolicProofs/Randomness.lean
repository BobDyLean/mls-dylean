module

public import MLS.Symbolic.SymbolicSpec.Randomness
public import MLS.Common.Proofs.Result
public import MLS.Common.Code.Crypto.Derived
import all MLS.Symbolic.SymbolicSpec.Randomness
import DY.Meta.Step

/-!
Port of the predicates and lemmas of `MLS.Symbolic.Randomness`:
the usages and labels of the random bytestrings given to the MLS functions.

Port-specific differences:
- MLS*'s randomness is indexed by the lengths of its bytestrings; here, `Randomness Bytes` is a list of bytes,
  and `RandomnessHasGhostData` requires the list of bytestrings and the ghost data to have the same length.
- `generate_randomness_proof` is the DyLean Hoare triple `generateRandomness.proof`, whose ghost argument is
  the ghost data (MLS*'s explicit argument `ldata` of `generate_randomness`).
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

/-- The ghost data of randomness stays true when the trace grows (MLS* uses SMT patterns). -/
public
theorem RandomnessHasGhostData_later (tr1 tr2: ProofTrace) (rand: Randomness Bytes) (ldata: RandomnessGhostData)
  : tr1 ≤ tr2 →
    RandomnessHasGhostData tr1 rand ldata →
    RandomnessHasGhostData tr2 rand ldata
:= by
  intro hle
  obtain ⟨l⟩ := rand
  simp only [RandomnessHasGhostData]
  induction l generalizing ldata with
  | nil => cases ldata <;> simp [RandomnessHasGhostData.go]
  | cons h t ih =>
    obtain _ | ⟨⟨usg, lab⟩, tdata⟩ := ldata
    · simp [RandomnessHasGhostData.go]
    · simp only [RandomnessHasGhostData.go]
      grind

grind_pattern RandomnessHasGhostData_later => tr1 ≤ tr2, RandomnessHasGhostData tr1 rand ldata
grind_pattern [grind_later] RandomnessHasGhostData_later => tr1 ≤ tr2, RandomnessHasGhostData tr1 rand ldata

section Generate

variable [ExecTraceTypes.Has Random.ExecEntryT]

public
instance (lengths: List Nat): HasGhostArgumentType (generateRandomness lengths: Traceful (Randomness Bytes)) RandomnessGhostData where
  dummy := ()

/--
Port of `generate_randomness_proof`.
MLS*'s refinement `List.Tot.length ldata == List.Tot.length l` is the precondition.
-/
@[instance]
public
theorem generateRandomness.proof [TraceInvariant] [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
  [BytesInvariants.Has DY.Random.invariants]
  (lengths: List Nat) (ldata: RandomnessGhostData):
  HoareTripleGhost
    (generateRandomness lengths)
    ldata
    (fun _ => ldata.length = lengths.length)
    (fun rand tr => RandomnessHasGhostData tr rand ldata)
:= by
  induction lengths generalizing ldata with
  | nil =>
    apply HoareTripleGhost.mk
    unfold generateRandomness
    step
    obtain rfl: ldata = [] := by grind
    subst x
    simp [RandomnessHasGhostData, RandomnessHasGhostData.go, mkEmptyRandomness]
  | cons h t ih =>
    obtain _ | ⟨⟨usg, lab⟩, tdata⟩ := ldata
    · apply HoareTripleGhost.mk
      intro tr hpre _
      simp at hpre
    · apply HoareTripleGhost.mk
      unfold generateRandomness
      step with ⟨ fun _ => lab, usg ⟩
      step with ⟨ tdata ⟩
      step
      subst x
      simp_all [RandomnessHasGhostData, RandomnessHasGhostData.go, mkRandomness]

end Generate

end MLS
