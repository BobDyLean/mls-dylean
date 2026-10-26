module

public import MLS.Symbolic.Code.Symbolic

/-!
Port of `MLS.Symbolic.Randomness`: generation of the randomness taken by the MLS functions.

Port-specific differences:
- The ghost data of MLS* (`randomness_ghost_data`: the usage and label of each random bytestring)
  is a ghost argument of the proofs in DyLean (`Random.genRand`):
  `generateRandomness` only takes the lengths of the random bytestrings (MLS*'s implicit `l`).
- The lemmas (`randomness_has_ghost_data`, …) are not ported yet.
-/

namespace MLS

open DY

variable [HasSymbolicBytes] [ExecTraceTypes] [ExecTraceTypes.Has Random.ExecEntryT]

/-- Port of `generate_randomness`. -/
public
def generateRandomness: List Nat → Traceful (Randomness Bytes)
  | [] => pure (mkEmptyRandomness Bytes)
  | h :: t => do
    let randCur ← Random.genRand h
    let randNext ← generateRandomness t
    pure (mkRandomness (randCur, randNext))

end MLS
