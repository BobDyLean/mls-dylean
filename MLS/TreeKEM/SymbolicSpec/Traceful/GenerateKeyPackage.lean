module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage`.

The function `generateKeyPackage` generates a new key package
given a "key package skeleton" given by the attacker.
More precisely, it obtains a key package from the network (the attacker),
replace its
- credential (via `generateLeafNode'`)
- signature key (via `generateLeafNode'`)
- leaf node key (via `generateLeafNode'`)
- init key (via `generateKeyPackage'`)
- signatures (leaf node & key package)
and send it back to the network.
The function `generateKeyPackage` further takes as input
a handle of the state of the signature key to use,
and outputs handles of the states of the leaf node key and init key.

Port-specific differences:
- MLS*'s functions with a leading underscore (`_generate_leaf_node`, …) end with a prime.
- DyLean's states are immutable: `generateKeyPackage` also returns the new handle of the key package store.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.Bootstrap

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-! ## Generate key package -/

/-- Port of `_generate_leaf_node`. -/
public
def generateLeafNode' (me: Participant) (leafNodeSkeleton: LeafNode Bytes tkt) (signatureKeySid: Nat):
  Traceful (LeafNode Bytes tkt × Nat)
:= do
  let some credential := principalToCredential me | failure
  let (leafNodeKeySid, leafNodeKey) ← mkLeafNodeKey me
  let signatureKey ← getSignatureKeyVk me signatureKeySid
  guard (leafNodeSkeleton.data.source = .keyPackage)
  let leafNodeKey ← extractResult (mkMlsBytes leafNodeKey "_generate_leaf_node" "leaf_node_key")
  let signatureKey ← extractResult (mkMlsBytes signatureKey "_generate_leaf_node" "signature_key")
  let leafNodeData: LeafNodeData Bytes tkt := {
    leafNodeSkeleton.data with
    credential
    content := (leafNodeKey: HpkePublicKey Bytes)
    signatureKey
  }
  -- MLS* knows that the source is `key_package`: the group identifier and leaf index are absent
  let leafNodeTbs: LeafNodeTBS Bytes tkt := {
    data := leafNodeData
    groupId := StaticOption.mk MlsBytes.empty
    leafIndex := StaticOption.mk 0
  }
  Symbolic.API.triggerLeafNodeEvent me leafNodeTbs
  let leafNode ← Symbolic.API.authenticateLeafNodeDataFromKeyPackage me signatureKeySid leafNodeData
  pure (leafNode, leafNodeKeySid)

/-- Port of `_sign_key_package`. -/
public
def signKeyPackage' (me: Participant) (keyPackageTbs: KeyPackageTBS Bytes tkt) (signatureKeySid: Nat):
  Traceful (KeyPackage Bytes tkt)
:= do
  let signatureKey ← getSignatureKeySk me signatureKeySid
  let signatureNonce ← Random.genRand (CryptoBytes.signSignMinEntropyLength Bytes)
  guard (BytesLike.length signatureNonce = CryptoBytes.signSignMinEntropyLength Bytes)
  let signature ← extractResult (signWithLabel signatureKey "KeyPackageTBS" (serializeNE (KeyPackageTBS.mf tkt) keyPackageTbs) signatureNonce)
  let signature ← extractResult (mkMlsBytes signature "_sign_key_package" "signature")
  pure {
    tbs := keyPackageTbs
    signature
  }

/-- Port of `key_package_private_state_ids`. -/
public
structure KeyPackagePrivateStateIds where
  signatureKeySid: Nat
  leafNodeKeySid: Nat
  initKeySid: Nat

/-- Port of `_generate_key_package`. -/
public
def generateKeyPackage' (me: Participant) (keyPackageSkeleton: KeyPackage Bytes tkt) (signatureKeySid: Nat):
  Traceful KeyPackageStoreValuePre
:= do
  let (leafNode, leafNodeKeySid) ← generateLeafNode' me keyPackageSkeleton.tbs.leafNode signatureKeySid
  let initKeySid ← mkInitKey me leafNode.data.content.val
  let initKey ← getInitKeyPk me initKeySid leafNode.data.content.val
  let initKey ← extractResult (mkMlsBytes initKey "_generate_key_package" "init_key")
  let keyPackageTbs: KeyPackageTBS Bytes tkt := {
    keyPackageSkeleton.tbs with
    leafNode
    initKey
  }
  let keyPackage ← signKeyPackage' me keyPackageTbs signatureKeySid
  pure {
    keyPackage
    signatureKeySid
    leafNodeKeySid
    initKeySid
  }

/--
Port of `generate_key_package`.
Returns the handle of the key package message, and the new handle of the key package store.
-/
public
def generateKeyPackage (me: Participant) (keyPackageSkeletonTs: Nat) (signatureKeySid: Nat) (keyPackageStoreSid: Nat):
  Traceful (Nat × Nat)
:= do
  let keyPackageSkeletonBytes ← Network.receiveMessage keyPackageSkeletonTs
  let some keyPackageSkeleton := (KeyPackage.mf tkt).toExtensible.parse keyPackageSkeletonBytes | failure
  let keyPackageStoreValue ← generateKeyPackage' me keyPackageSkeleton signatureKeySid
  let keyPackageStoreSid ← extendKeyPackageStore me keyPackageStoreSid keyPackageStoreValue
  let keyPackageTs ← Network.sendMessage (serializeNE (KeyPackage.mf tkt) keyPackageStoreValue.keyPackage)
  pure (keyPackageTs, keyPackageStoreSid)

end MLS.TreeKEM
