module

public import MLS.Symbolic.Code.Symbolic
import all MLS.Symbolic.Code.Symbolic
import all DY.Trace.Manipulation
import DY.Meta.Step

/-!
Proofs about the traceful functions of `MLS.Symbolic` (`MLS/Symbolic/Code/Symbolic.lean`):
the Hoare triple of `extractResult`, which MLS* proves by unfolding it,
a Hoare triple of DyLean's `getTimestamp` giving its result,
and the Hoare triple of `List.foldlM` (MLS*'s `fold_leftM_proof`, from `MLS.TreeKEM.Symbolic.Traceful.ProcessCommit.Proof`).
-/

namespace MLS

open DY

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]

/-- Hoare triple of `extract_result`: the result is the value of a successful computation. -/
@[instance]
public
theorem extractResult.proof {α: Type} (x: Result α):
  HoareTriple
    (extractResult x)
    (fun _ => True)
    (fun y _ => x = .success y)
:= by
  unfold extractResult
  split
  · step
    grind
  · step

/--
Hoare triple of DyLean's `getTimestamp`, giving its result: the length of the trace.
Its postcondition cannot be monotonized: it is not an instance (use it with `attribute [local instance]`),
and is only useful for the next action.
-/
public
theorem getTimestamp.proof_eq:
  HoareTriple
    getTimestamp
    (fun _ => True)
    (fun time tr => time = tr.length)
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, WP.wp, getTimestamp, Traceful.run_mk]
  intro tr _ _
  exists tr
  simp_all [Trace.erase_length, Trace.le_refl]

/--
The ghost argument of the Hoare triple of `List.foldlM` (as DyLean's `LoopInvariantAndProof` for `forIn`):
an invariant of the cursor in the list and of the accumulator, preserved by each call of `f`.
-/
public
structure FoldlMInvariantAndProof {α β: Type} (xs: List β) (f: α → β → Traceful α) where
  inv: List.Cursor xs × α → ProofTrace → Prop
  step:
    ∀ pref cur suff (h: xs = pref ++ cur :: suff) acc,
      HoareTriple
        (f acc cur)
        (inv (⟨pref, cur :: suff, h.symm⟩, acc))
        (fun res => inv (⟨pref ++ [cur], suff, by simp [h]⟩, res))

public
instance {α β: Type} (xs: List β) (init: α) (f: α → β → Traceful α):
  HasGhostArgumentType (xs.foldlM f init) (FoldlMInvariantAndProof xs f)
where
  dummy := ()

/--
Port of `fold_leftM_proof` (MLS*'s `fold_leftM` is Lean's `List.foldlM`).
MLS*'s invariants of the elements (`l_invariant`) and of the accumulator (`acc_invariant`) are one invariant
of the cursor and of the accumulator, given as a ghost argument (as DyLean's `forIn.proof`).
-/
@[instance]
public
theorem foldlM.proof {α β: Type} (xs: List β) (init: α) {f: α → β → Traceful α}
  (invAndProof: FoldlMInvariantAndProof xs f):
  HoareTripleGhost
    (xs.foldlM f init)
    invAndProof
    (invAndProof.inv (⟨[], xs, rfl⟩, init))
    (fun res => invAndProof.inv (⟨xs, [], by simp⟩, res))
:= by
  apply HoareTripleGhost.mk
  suffices h: ∀ c: List.Cursor xs,
    hoareTriple (c.suffix.foldlM f init) (invAndProof.inv (c, init)) (fun res => invAndProof.inv (⟨xs, [], by simp⟩, res))
  from h ⟨[], xs, rfl⟩
  intro ⟨pref, suff, h⟩
  induction suff generalizing pref init with
  | nil =>
    intro tr hinv _
    exists tr
    simp only [List.append_nil] at h
    subst h
    simp [List.foldlM_nil, Traceful.run_pure, hinv]
    grind
  | cons cur tail ih =>
    intro tr hinv htr
    have := invAndProof.step pref cur tail h.symm init
    simp only [List.foldlM_cons]
    apply Traceful.bind_wp () (f init cur) _ _ tr htr hinv
    intro tr' res hres htr' _
    exact ih res (pref ++ [cur]) (by simp [h]) tr' hres htr'

end MLS
