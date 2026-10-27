module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeDEM.Code.NetworkTypes
public import MLS.Common.Code.Crypto.Derived
public import DySlop.Lib.State.Map

/-!
Port of `MLS.TreeKEM.Symbolic.State.ProposalCache`: a map from proposal references to the proposals and their senders.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated,
  hence `rememberProposal` returns the new handle of the map.
- The invariants (`proposal_cache_pred`, …) and the proofs are in `MLS.TreeKEM.SymbolicProofs.State.ProposalCache`.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeDEM
open DySlop.Map (MapTypes Map)

variable [HasSymbolicBytes]

/-- Port of `proposal_cache_key`. -/
public
structure ProposalCacheKey where
  proposalRef: Bytes

namespace ProposalCacheKey

public
def f: Bytes → ProposalCacheKey :=
  fun proposalRef => { proposalRef }

public
def g: ProposalCacheKey → Bytes :=
  fun x => x.proposalRef

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end ProposalCacheKey

/-- Port of `ps_proposal_cache_key`. -/
public
def ProposalCacheKey.mf: NonExtensibleMessageFormat Bytes ProposalCacheKey :=
  .isomorphic .slowBytes ProposalCacheKey.f ProposalCacheKey.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_proposal_cache_key_is_well_formed`. -/
@[simp]
public
theorem ProposalCacheKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ProposalCacheKey):
  ProposalCacheKey.mf.wf pred x = pred x.proposalRef
:= by
  simp [ProposalCacheKey.mf, ProposalCacheKey.g]

/-- Port of `proposal_and_sender`. -/
public
structure ProposalAndSender where
  proposal: Proposal Bytes
  sender: Nat

namespace ProposalAndSender

public
def f: Proposal Bytes × Nat → ProposalAndSender :=
  fun (proposal, sender) => { proposal, sender }

public
def g: ProposalAndSender → Proposal Bytes × Nat :=
  fun { proposal, sender } => (proposal, sender)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end ProposalAndSender

/-- Port of `ps_proposal_and_sender`. -/
public
def ProposalAndSender.mf: NonExtensibleMessageFormat Bytes ProposalAndSender :=
  .isomorphic (.prod Proposal.mf .slowNat) ProposalAndSender.f ProposalAndSender.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_proposal_and_sender_is_well_formed`. -/
@[simp]
public
theorem ProposalAndSender.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ProposalAndSender):
  ProposalAndSender.mf.wf pred x = Proposal.mf.wf pred x.proposal
:= by
  simp only [ProposalAndSender.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, ProposalAndSender.g,
    NonExtensibleMessageFormat.prod.wf_eq, NonExtensibleMessageFormat.slowNat.wf_eq, and_true]

/-- Port of `proposal_cache_types`. -/
public
instance proposalCacheTypes: MapTypes ProposalCacheKey ProposalAndSender where
  mfKey := ProposalCacheKey.mf
  mfValue := ProposalAndSender.mf

/-! ## Proposal cache API -/

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map ProposalCacheKey ProposalAndSender))]

/-- Port of `initialize_proposal_cache`. -/
public
def initializeProposalCache (prin: Participant): Traceful Nat :=
  DySlop.Map.initializeMap ProposalCacheKey ProposalAndSender prin

/-- Port of `_retrieve_one_proposal`. -/
public
def retrieveOneProposal' (me: Participant) (sid: Nat) (myIndex: Nat) (proposalOrRef: ProposalOrRef Bytes):
  Traceful ProposalAndSender
:=
  match proposalOrRef with
  | .proposal proposal => pure { proposal, sender := myIndex }
  | .reference proposalRef => DySlop.Map.findValue me sid ({ proposalRef := proposalRef.val }: ProposalCacheKey)

/-- Port of `retrieve_proposals`. -/
public
def retrieveProposals (me: Participant) (sid: Nat) (myIndex: Nat):
  List (ProposalOrRef Bytes) → Traceful (List ProposalAndSender)
  | [] => pure []
  | h :: t => do
    let resH ← retrieveOneProposal' me sid myIndex h
    let resT ← retrieveProposals me sid myIndex t
    pure (resH :: resT)

/--
Port of `remember_proposal`.
Returns the new handle of the proposal cache.
-/
public
def rememberProposal (me: Participant) (sid: Nat) (proposal: Proposal Bytes) (sender: Nat): Traceful Nat := do
  let proposalRef ← extractResult (makeProposalRef (serializeNE Proposal.mf proposal))
  let key: ProposalCacheKey := { proposalRef }
  let value: ProposalAndSender := { proposal, sender }
  DySlop.Map.addKeyValue me sid key value

end MLS.TreeKEM
