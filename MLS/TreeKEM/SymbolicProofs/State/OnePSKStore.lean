module

public import MLS.TreeKEM.SymbolicSpec.State.OnePSKStore

/-!
Port of the labels of `MLS.TreeKEM.Symbolic.State.OnePSKStore`: the label of pre-shared keys.

Port-specific differences:
- DY*'s `typed_state_pred_label (psk_label_input prin psk_id)` is a DyLean label
  whose corruption is the compromise of a PSK state of `prin` with the PSK identifier `psk_id`
  (as `MLS.TreeSync.signatureKeyLabel`); `psk_label_input` is inlined in `pskLabel`.
- The state invariant (`one_psk_state_pred`) and the proofs of the traceful functions are not ported yet.
-/

namespace MLS.TreeKEM

open DY
open MLS

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

end MLS.TreeKEM
