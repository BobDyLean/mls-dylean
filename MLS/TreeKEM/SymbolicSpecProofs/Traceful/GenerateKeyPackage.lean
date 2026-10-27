module

public import MLS.TreeKEM.SymbolicSpec.Traceful.GenerateKeyPackage
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants
public import MLS.TreeSync.SymbolicProofs.AuthService.CredentialInterpretation
import all MLS.TreeKEM.SymbolicSpec.Traceful.GenerateKeyPackage
import DY.Meta.Step

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage.Proof`.

Port-specific differences:
- The proofs are DyLean Hoare triples (instances), assuming the invariants of
  `MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants` (MLS*'s `has_treesync_and_treekem_invariants`).
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.Bootstrap

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]
variable [HasTreesyncInvariants tkt] [HasTreeKEMProofTrace]
variable [HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants]

/-! ## Generate key package, proof -/

omit [HasKeyPackageInvariant] in
/-- Port of `_generate_leaf_node_proof`. -/
@[instance]
public
theorem generateLeafNode'.proof (me: Participant) (leafNodeSkeleton: LeafNode Bytes tkt) (signatureKeySid: Nat):
  HoareTriple
    (generateLeafNode' me leafNodeSkeleton signatureKeySid)
    (fun tr => (LeafNode.mf tkt).wf (Bytes.Publishable · tr) leafNodeSkeleton)
    (fun (leafNode, _leafNodeKeySid) tr =>
      (LeafNode.mf tkt).wf (Bytes.Publishable · tr) leafNode ∧
      credentialToPrincipal leafNode.data.credential = some me
    )
:= by
  unfold generateLeafNode'
  split
  · step
    split
    step
    step
    step
    step
    step_intro
    step_intro
    step by
      rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := leafNodeSignedEventPred)]
      simp only [leafNodeSignedEventPred, leafNodeTbs, leafNodeData, ‹leafNodeSkeleton.data.source = _›]
      grind [IsNodePkForLeafPk, mkMlsBytes_eq_success]
    step by
      have := principalToCredential_wf tr me credential ‹_›
      have hsk := ‹(LeafNode.mf tkt).wf (Bytes.Publishable · tr) leafNodeSkeleton›
      simp only [LeafNode.mf.wf_eq, LeafNodeData.mf.wf_eq] at hsk
      refine ⟨?_, ‹_›⟩
      simp only [leafNodeData, LeafNodeData.mf.wf_eq]
      grind [IsSignatureKeyVk, IsNodePkForLeafPk, mkMlsBytes_eq_success, tkt.mfLeafContent.wf_eq]
    step
    grind [credentialToPrincipal_principalToCredential]
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr

omit [HasTreeKEMProofTrace] [HasTreesyncTreekemLinkInvariants] in
/--
Port of `_sign_key_package_proof`.
It also states that the signed content of the key package is `keyPackageTbs`.
-/
@[instance]
public
theorem signKeyPackage'.proof (me: Participant) (keyPackageTbs: KeyPackageTBS Bytes tkt) (signatureKeySid: Nat):
  HoareTriple
    (signKeyPackage' me keyPackageTbs signatureKeySid)
    (fun tr =>
      IsInitKeyPk tr me keyPackageTbs.leafNode.data.content.val keyPackageTbs.initKey.val ∧
      (KeyPackageTBS.mf tkt).wf (Bytes.Publishable · tr) keyPackageTbs
    )
    (fun keyPackage tr =>
      (KeyPackage.mf tkt).wf (Bytes.Publishable · tr) keyPackage ∧
      keyPackage.tbs = keyPackageTbs
    )
:= by
  unfold signKeyPackage'
  step
  step with ⟨ fun _ => Label.secret, Usage.sigNonce ⟩
  step
  step
  step
  step
  obtain ⟨hinit, htbs⟩ := ‹IsInitKeyPk tr me _ _ ∧ _›
  have hmsg := (pred_serializeNE_iff (KeyPackageTBS.mf tkt) (Bytes.Publishable · tr) keyPackageTbs).2 htbs
  have hs := signWithLabel.Invariant keyPackageSignPred tr me signatureKey "KeyPackageTBS" _ signatureNonce _
    ‹_› (by grind [IsSignatureKeySk]) (by grind) hmsg.1 (by grind [IsSignatureKeySk]) ‹_› (by grind) (by simp)
    (Or.inl ((keyPackageTbsPred_serializeNE me keyPackageTbs tr).2 (by grind [IsInitKeyPk])))
  simp only [KeyPackage.mf.wf_eq]
  grind [mkMlsBytes_eq_success, canFlowTrans]

/-- Port of `_generate_key_package_proof`. -/
@[instance]
public
theorem generateKeyPackage'.proof (me: Participant) (keyPackageSkeleton: KeyPackage Bytes tkt) (signatureKeySid: Nat):
  HoareTriple
    (generateKeyPackage' me keyPackageSkeleton signatureKeySid)
    (fun tr => (KeyPackage.mf tkt).wf (Bytes.Publishable · tr) keyPackageSkeleton)
    (fun keyPackageStoreValue tr =>
      (KeyPackage.mf tkt).wf (Bytes.Publishable · tr) keyPackageStoreValue.keyPackage ∧
      credentialToPrincipal keyPackageStoreValue.keyPackage.tbs.leafNode.data.credential = some me
    )
:= by
  unfold generateKeyPackage'
  step by
    simp only [KeyPackage.mf.wf_eq, KeyPackageTBS.mf.wf_eq] at *
    grind
  split
  step by
    simp only [LeafNode.mf.wf_eq, LeafNodeData.mf.wf_eq] at *
    grind [tkt.mfLeafContent.wf_eq]
  step
  step
  step_intro
  step by
    simp only [keyPackageTbs, KeyPackageTBS.mf.wf_eq, KeyPackage.mf.wf_eq] at *
    grind [mkMlsBytes_eq_success, IsInitKeyPk]
  step
  grind

/-- Port of `generate_key_package_proof`. -/
@[instance]
public
theorem generateKeyPackage.proof (me: Participant) (keyPackageSkeletonTs: Nat) (signatureKeySid: Nat)
  (keyPackageStoreSid: Nat):
  HoareTriple
    (generateKeyPackage me keyPackageSkeletonTs signatureKeySid keyPackageStoreSid)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold generateKeyPackage
  step
  split
  · step by
      apply wf_of_parse _ _ _ _ ‹_› ‹_›
    step
    step by
      exact (pred_serializeNE_iff _ _ _).2 ‹_›
    step
    trivial
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

end MLS.TreeKEM
