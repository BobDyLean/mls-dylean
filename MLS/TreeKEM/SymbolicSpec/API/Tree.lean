module

public import MLS.TreeKEM.Code.API
public import MLS.Symbolic.Code.Symbolic

/-!
Port of `MLS.TreeKEM.Symbolic.API.Tree` (its traceful function).

Port-specific differences:
- The invariants (`treekem_tree_state_invariant`, …) and the proofs of the non-traceful functions are in
  `MLS.TreeKEM.SymbolicProofs.API.Tree`; the proof of the traceful function (`generate_prepare_create_commit_rand_good`)
  is in `MLS.TreeKEM.SymbolicSpecProofs.API.Tree`.
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
