import MLS.TreeKEM.Code.API.KeySchedule.Types
import MLS.TreeKEM.Code.API.Tree.Types

/-!
Port of `MLS.TreeKEM.API.Types`.

Port-specific differences:
- `treekem_index st` (`i:nat{i < pow2 st.tree_state.levels}`) is `Nat`.
-/

namespace MLS.TreeKEM

/-- Port of `treekem_state`. -/
structure TreeKEMState (Bytes: Type) (leafInd: Nat) where
  treeState: TreeKEMTreeState Bytes leafInd
  keyscheduleState: TreeKEMKeyscheduleState Bytes

end MLS.TreeKEM
