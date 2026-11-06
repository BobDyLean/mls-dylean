module

public import MLS.Common.Code.Crypto.Builtins
public import MLS.TreeSync.Code.Invariants.AuthService

/-!
Port of `MLS.TreeSync.API.Types`.

Port-specific differences:
- MLS*'s `Refined` interface is not ported: the tree of the state is a plain `TreeSync` tree
  (MLS*'s `treesync_valid`, which also carries the TreeSync invariants).
- `treesync_index st` (`i:nat{i < pow2 st.levels}`) is `Nat`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

/-- Port of `treesync_state`. -/
public
structure TreeSyncState (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) (TokenT: Type) (groupId: MlsBytes Bytes) where
  levels: Nat
  tree: TreeSync Bytes tkt levels
  tokens: ASTokens TokenT levels

/--
Port of `treesync_state_valid`.
Unlike MLS*, it also states that the tree and the tokens have the same position
(both are at position `0` in MLS*, by typing).
-/
@[expose]
public
def treesyncStateValid {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes} {TokenT: Type} {groupId: MlsBytes Bytes}
  (asp: ASParameters Bytes TokenT) (st: TreeSyncState Bytes tkt TokenT groupId): Prop
:=
  st.tree.position = st.tokens.position ∧ allCredentialsOk asp st.tree st.tokens

end MLS.TreeSync
