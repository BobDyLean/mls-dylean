import MLS.TreeKEM.Code.Types

/-!
Port of `MLS.TreeKEM.API.Tree.Types`.

Port-specific differences:
- The refinements of `treekem_tree_state` (`leaf_ind < pow2 levels`, `treekem_invariant tree`
  and `treekem_priv_invariant tree priv`) are the predicate `TreeKEMTreeState.Valid` (in `MLS.TreeKEM.Proofs.API.Tree`).
- `treekem_index st` (`i:nat{i < pow2 st.levels}`) is `Nat`.
-/

namespace MLS.TreeKEM

/-- Port of `treekem_tree_state`. -/
structure TreeKEMTreeState (Bytes: Type) (leafInd: Nat) where
  levels: Nat
  tree: TreeKEM Bytes levels
  priv: TreeKEMPriv Bytes levels

end MLS.TreeKEM
