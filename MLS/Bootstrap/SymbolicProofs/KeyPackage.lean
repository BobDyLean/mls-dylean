module

public import MLS.Bootstrap.SymbolicSpec.KeyPackage
public import MLS.Bootstrap.SymbolicProofs.State.InitKey
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import DySlop.Lib.Label

/-!
Port of the labels of `MLS.Bootstrap.Symbolic.KeyPackage`:
the label of the init key of a key package, and the label of the init key associated with a leaf node.

Port-specific differences:
- DY*'s `event_triggered_label prin {key_package}` is DyLean's `ProtocolEvent.label` of the event
  (whose principal is the field `prin`).
- Only the labels are ported for now: the signature predicate (`key_package_sign_pred`),
  the event predicate (`key_package_has_been_verified_pred`) and the lemmas
  (`key_package_to_init_label_lemma`, `init_key_associated_with_lemma`, …) are not ported yet.
-/

namespace MLS.Bootstrap

open DY
open MLS MLS.TreeSync

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]

/-! ## KeyPackage label -/

/-- Port of `principal_key_package_has_been_verified_label`. -/
@[expose]
public
def principalKeyPackageHasBeenVerifiedLabel (keyPackage: KeyPackage Bytes TreeKEM.tkt) (prin: Participant): Label :=
  ProtocolEvent.label ({ prin, keyPackage }: KeyPackageHasBeenVerified)

/-- Port of `key_package_has_been_verified_label`. -/
@[expose]
public
def keyPackageHasBeenVerifiedLabel (keyPackage: KeyPackage Bytes TreeKEM.tkt): Label :=
  Label.bigJoin (principalKeyPackageHasBeenVerifiedLabel keyPackage)

/-- Port of `key_package_to_principal`. -/
@[expose]
public
def keyPackageToPrincipal (kp: KeyPackage Bytes TreeKEM.tkt): Option Participant :=
  credentialToPrincipal kp.tbs.leafNode.data.credential

/-- Port of `key_package_to_init_label`. -/
@[expose]
public
def keyPackageToInitLabel (kp: KeyPackage Bytes TreeKEM.tkt): Label :=
  match keyPackageToPrincipal kp with
  | none => Label.pub
  | some prin =>
    (Label.guarded (signatureKeyLabel prin kp.tbs.leafNode.data.signatureKey.val) (keyPackageHasBeenVerifiedLabel kp)).join
      (initKeyLabel prin kp.tbs.initKey.val)

/-! ## Init key associated to leaf node -/

/-- Port of `key_package_has_leaf_node`. -/
@[expose]
public
def KeyPackageHasLeafNode (kp: KeyPackage Bytes TreeKEM.tkt) (ln: LeafNode Bytes TreeKEM.tkt): Prop :=
  kp.tbs.leafNode = ln

/-- Port of `init_key_associated_with_aux`. -/
@[expose]
public
def initKeyAssociatedWithAux (ln: LeafNode Bytes TreeKEM.tkt) (kp: KeyPackage Bytes TreeKEM.tkt): Label :=
  ((Label.ofProp (KeyPackageHasLeafNode kp ln)).meet (keyPackageHasBeenVerifiedLabel kp)).meet (keyPackageToInitLabel kp)

/-- Port of `init_key_associated_with`. -/
@[expose]
public
def initKeyAssociatedWith (ln: LeafNode Bytes TreeKEM.tkt): Label :=
  Label.bigJoin (initKeyAssociatedWithAux ln)

end MLS.Bootstrap
