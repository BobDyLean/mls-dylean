module

public import MLS.TreeKEM.SymbolicSpec.API.Tree
public import MLS.TreeKEM.SymbolicProofs.API.Tree
import all MLS.TreeKEM.SymbolicSpec.API.Tree
import DY.Meta.Step

/-!
Port of the proof of the traceful function of `MLS.TreeKEM.Symbolic.API.Tree`
(`generate_prepare_create_commit_rand_good`).

Port-specific differences:
- The proof is a DyLean Hoare triple (an instance), whose ghost argument is MLS*'s `path_usages`
  (not an argument of `generatePrepareCreateCommitRand`, see `MLS.TreeKEM.SymbolicSpec.API.Tree`).
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync MLS.TreeKEM.Symbolic.API.Tree

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

public
instance (me: Participant): HasGhostArgumentType (generatePrepareCreateCommitRand me) PathSecretUsage where
  dummy := ()

variable [TraceInvariant] [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has DY.Random.invariants]

/-- Port of `generate_prepare_create_commit_rand_good`. -/
@[instance]
public
theorem generatePrepareCreateCommitRand.proof (me: Participant) (pathUsages: PathSecretUsage):
  HoareTripleGhost
    (generatePrepareCreateCommitRand me)
    pathUsages
    (fun _ => True)
    (fun randPrepare tr => PrepareCreateCommitRandGood tr me randPrepare pathUsages)
:= by
  apply HoareTripleGhost.mk
  unfold generatePrepareCreateCommitRand
  step with ⟨ leafSkMyMkRandLabel me, nodeKeyUsage ⟩
  step with ⟨ fun _ => (nodeKeyLabel me (DySlop.HPKE.hpkePk leafSk)).join (PathSecretUsage.headLabel pathUsages),
    PathSecretUsage.toUsage pathUsages.tail ⟩
  step
  subst x
  intro leafSk' rand1 h1 pathSecret0' rand2 h2
  simp only [destRandomness, mkRandomness, Result.pure_eq_success, Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := h2
  grind [leafSkMyMkRandLabel]

end MLS.TreeKEM
