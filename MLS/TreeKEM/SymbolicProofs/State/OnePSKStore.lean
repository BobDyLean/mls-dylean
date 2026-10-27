module

public import MLS.TreeKEM.SymbolicSpec.State.OnePSKStore
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeKEM.SymbolicSpec.State.OnePSKStore
import DY.Meta.Step

/-!
Port of the labels, invariant and proofs of `MLS.TreeKEM.Symbolic.State.OnePSKStore`:
the label of pre-shared keys, the invariant of PSK states, and the proofs of the traceful functions.

Port-specific differences:
- DY*'s `typed_state_pred_label (psk_label_input prin psk_id)` is a DyLean label
  whose corruption is the compromise of a PSK state of `prin` with the PSK identifier `psk_id`
  (as `MLS.TreeSync.signatureKeyLabel`); `psk_label_input` is inlined in `pskLabel`.
- The state predicate (`one_psk_state_pred`) is the DyLean state invariant `onePskStateInv`
  (an instance, as in DyLean's examples): MLS*'s `has_one_psk_state_invariant` is not needed.
- The proofs of the traceful functions (`get_psk_proof`, `store_psk_proof`) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the state. The `tr_out == tr` part of their postconditions is not ported.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open MLS

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OnePskState)]

/--
Port of `psk_label` (with `psk_label_input`):
the pre-shared key of `prin` with identifier `pskId` is corrupt
when a PSK state of `prin` with this identifier is compromised.
-/
@[expose]
public
def pskLabel (prin: Participant) (pskId: PreSharedKeyIdShort): Label where
  isCorrupt tr := ∃ psk, PersistentLocalState.LocalStateCompromised prin ({ pskId, psk }: OnePskState) tr

end Labels

section StateInvariant

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OnePskState)]

/-- Port of `one_psk_state_pred`: the invariant of PSK states. -/
public
instance onePskStateInv: PersistentLocalState.CompromisableLocalStateInv OnePskState where
  invariant me st tr :=
    PreSharedKeyIdShort.mf.wf (Bytes.Publishable · tr) st.pskId ∧
    st.psk.KnowableBy (pskLabel me st.pskId) tr
  invariant_later me st tr1 tr2 := by
    grind
  invariant_implies_KnowableBy me st tr h := by
    obtain ⟨pskId, psk⟩ := st
    have hflow: (pskLabel me pskId).canFlow
        (PersistentLocalState.label me ({ pskId, psk }: OnePskState)) tr.erase := by
      simp only [Label.canFlow, pskLabel]
      grind
    have := wf_knowableBy_of_publishable PreSharedKeyIdShort.mf
      (PersistentLocalState.label me ({ pskId, psk }: OnePskState)) tr pskId h.1
    simp only [DY.Comparse.IsWellFormed, DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
      NonExtensibleMessageFormat.toExtensible.wf_eq, OnePskState.mf.wf_eq]
    grind [Bytes.KnowableBy, canFlowTrans]

end StateInvariant

section Proofs

open PersistentLocalState

variable [HasSymbolicInvariants] [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT OnePskState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT OnePskState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT OnePskState)]

/-- Port of `get_psk_proof`. -/
@[instance]
public
theorem getPsk.proof (me: Participant) (pskSid: Nat):
  HoareTriple
    (getPsk me pskSid)
    (fun _ => True)
    (fun (pskId, psk) tr => psk.KnowableBy (pskLabel me pskId) tr)
:= by
  unfold getPsk
  step
  step
  simp only [LocalStateInv.invariant] at *
  grind

/-- Port of `store_psk_proof`. -/
@[instance]
public
theorem storePsk.proof (me: Participant) (pskId: PreSharedKeyIdShort) (psk: Bytes):
  HoareTriple
    (storePsk me pskId psk)
    (fun tr =>
      PreSharedKeyIdShort.mf.wf (Bytes.Publishable · tr) pskId ∧
      psk.KnowableBy (pskLabel me pskId) tr
    )
    (fun _ _ => True)
:= by
  unfold storePsk
  step by
    simp only [LocalStateInv.invariant]
    grind
  trivial

end Proofs

end MLS.TreeKEM
