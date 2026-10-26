module

public import MLS.TreeSync.SymbolicSpec.API
public import MLS.TreeSync.Proofs.ParentHashGuarantees

/-!
Port of the predicates of `MLS.TreeSync.Symbolic.API`: the preconditions of the functions triggering events.

Port-specific differences:
- The namespace is `MLS.TreeSync.Symbolic.API` (MLS*'s module name), as in `MLS.TreeSync.SymbolicSpec.API`.
- DY*'s event predicates (`event_predicate`) take the principal in the event:
  they are functions `ProofTrace → Event → Prop`, as DyLean's event invariants.
- MLS*'s `match`es on results are hypotheses (`… = .success authP → …`).
- The invariants (`has_treesync_invariants`, …) and the proofs (`*_proof`) are not ported yet.
-/

namespace MLS.TreeSync.Symbolic.API

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}

/-- Port of `tree_event_pre`. -/
@[expose]
public
def TreeEventPre (tr: ProofTrace) (groupHasEventPred: ProofTrace → GroupHasTreeEvent tkt → Prop) (p: Participant)
  (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (t: OneTreeSync Bytes tkt): Prop :=
  ∀ tr', tr ≤ tr' → groupHasEventPred tr' (mkGroupHasTreeEvent p groupId authentifierLeafIndex t)

/--
Port of `external_path_has_event_pre`.
MLS*'s leaf index `li` (implicit in the path) is explicit.
-/
@[expose]
public
def ExternalPathHasEventPre {l: Nat}
  (leafNodeHasEventPred: ProofTrace → LeafNodeSignedEvent tkt → Prop)
  (groupHasEventPred: ProofTrace → GroupHasTreeEvent tkt → Prop)
  (tr: ProofTrace) (prin: Participant) (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes): Prop :=
  p.getPathLeaf.source = .update →
  li < 2^32 →
  ∀ authP, externalPathToPathNosig t li p = .success authP →
    let authLn := authP.getPathLeaf
    leafNodeHasEventPred tr
      { prin, lnTbs := { data := authLn.data, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 } } ∧
    PathToTreeListPre (TreeEventPre tr groupHasEventPred prin groupId li) t li authP

end MLS.TreeSync.Symbolic.API
