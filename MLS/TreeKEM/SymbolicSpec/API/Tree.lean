module

public import MLS.TreeKEM.Code.API
public import MLS.Symbolic.Code.Symbolic

/-!
Port of `MLS.TreeKEM.Symbolic.API.Tree` (its traceful function).

Port-specific differences:
- Only the specification is ported for now: the invariants (`treekem_tree_state_invariant`, …) and the proofs are not ported yet.
-/

namespace MLS.TreeKEM

open DY
open MLS

variable [HasSymbolicBytes] [ExecTraceTypes] [ExecTraceTypes.Has Random.ExecEntryT]

/--
Port of `generate_prepare_create_commit_rand`.
MLS*'s argument `path_usages` only determines the usages and labels of the randomness,
which are ghost arguments of the proofs in DyLean (`Random.genRand`): it is not ported.
-/
public
def generatePrepareCreateCommitRand (_me: Participant): Traceful (Randomness Bytes) := do
  let leafSk ← Random.genRand (CryptoBytes.hpkePrivateKeyLength Bytes)
  let pathSecret0 ← Random.genRand (CryptoBytes.kdfLength Bytes)
  pure (mkRandomness (leafSk, mkRandomness (pathSecret0, mkEmptyRandomness Bytes)))

end MLS.TreeKEM
