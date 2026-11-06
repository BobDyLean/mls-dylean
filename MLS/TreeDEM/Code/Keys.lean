module

public import MLS.Common.Code.Crypto.Derived
public import MLS.Common.Code.Tree

/-!
Port of `MLS.TreeDEM.Keys`.

Port-specific differences:
- `leaf_kdf` takes the height `l` and position `i` of the tree (implicit in MLS*'s `leaf_index l i`) explicitly.
- `init_ratchet_state` (a ratchet state with generation `0`) is `RatchetState`.
- Secrets, keys and nonces are `Bytes` (see `MLS.Crypto.Builtins`).
-/

namespace MLS.TreeDEM

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

public
structure TreeContext where
  generation: UInt32

public
instance: LeftInverse TreeContext.generation TreeContext.mk := ⟨by intro _; rfl⟩
public
instance: RightInverse TreeContext.generation TreeContext.mk := ⟨by intro _; rfl⟩

@[expose]
public
def TreeContext.mf {Bytes: Type} [BytesLike Bytes]: NonExtensibleMessageFormat Bytes TreeContext :=
  .isomorphic .uint32BE TreeContext.mk TreeContext.generation
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem TreeContext.mf.wf_eq {Bytes: Type} [BytesLike Bytes] (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeContext):
  (TreeContext.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [TreeContext.mf]

/-- Port of `derive_tree_secret`. -/
@[expose]
public
def deriveTreeSecret (secret: Bytes) (label: String) (generation: Nat) (len: Nat): Result Bytes := do
  let generation ← mkUInt32 generation "derive_tree_secret" "generation"
  let treeContext := serializeNE TreeContext.mf { generation }
  expandWithLabel secret label treeContext len

/--
Port of `leaf_kdf`.
MLS* requires `leaf_index: leaf_index l i` (i.e. `i ≤ leafIndex < i + 2^l`);
otherwise, the function follows the path to the leaf closest to `leafIndex`.
-/
@[expose]
public
def leafKdf (encryptionSecret: Bytes) (l i: Nat) (leafIndex: Nat): Result Bytes :=
  match l with
  | 0 => pure encryptionSecret
  | l+1 => do
    let dirString := if isLeftLeaf (l+1) i leafIndex then "left" else "right"
    let newI := if isLeftLeaf (l+1) i leafIndex then leftIndex i else rightIndex (l+1) i
    let newEncryptionSecret ← expandWithLabel encryptionSecret "tree" (CryptoBytes.stringToBytes dirString) (CryptoBytes.kdfLength Bytes)
    leafKdf newEncryptionSecret l newI leafIndex

/-- Port of `ratchet_state`. -/
public
structure RatchetState (Bytes: Type) where
  secret: Bytes
  generation: Nat

/-- Port of `ratchet_output`. -/
public
structure RatchetOutput (Bytes: Type) where
  nonce: Bytes
  key: Bytes

/-- Port of `init_handshake_ratchet`. -/
@[expose]
public
def initHandshakeRatchet (treeNodeSecret: Bytes): Result (RatchetState Bytes) := do
  let ratchetSecret ← expandWithLabel treeNodeSecret "handshake" (CryptoBytes.stringToBytes "") (CryptoBytes.kdfLength Bytes)
  pure {
    secret := ratchetSecret
    generation := 0
  }

/--
Port of `init_application_ratchet`.
TODO (as in MLS*): this is a copy-paste of init_handeshake_ratchet, factorize?
-/
@[expose]
public
def initApplicationRatchet (treeNodeSecret: Bytes): Result (RatchetState Bytes) := do
  let ratchetSecret ← expandWithLabel treeNodeSecret "application" (CryptoBytes.stringToBytes "") (CryptoBytes.kdfLength Bytes)
  pure {
    secret := ratchetSecret
    generation := 0
  }

/-- Port of `ratchet_get_key`. -/
@[expose]
public
def ratchetGetKey (st: RatchetState Bytes): Result (RatchetOutput Bytes) := do
  let nonce ← deriveTreeSecret st.secret "nonce" st.generation (CryptoBytes.aeadNonceLength Bytes)
  let key ← deriveTreeSecret st.secret "key" st.generation (CryptoBytes.aeadKeyLength Bytes)
  pure {
    nonce
    key
  }

/-- Port of `ratchet_next_state`. -/
@[expose]
public
def ratchetNextState (st: RatchetState Bytes): Result (RatchetState Bytes) := do
  let newSecret ← deriveTreeSecret st.secret "secret" st.generation (CryptoBytes.kdfLength Bytes)
  pure {
    secret := newSecret
    generation := st.generation + 1
  }

/-- `ratchetNextState` increments the generation (needed for the termination of `ratchetGetGenerationKey`). -/
theorem ratchetNextState_generation (st st': RatchetState Bytes) (h: ratchetNextState st = .success st'):
  st'.generation = st.generation + 1
:= by
  unfold ratchetNextState at h
  cases h': deriveTreeSecret st.secret "secret" st.generation (CryptoBytes.kdfLength Bytes) <;>
    simp_all [Bind.bind, Result.bind, pure] <;> grind

/--
Port of `ratchet_get_generation_key`.
MLS* requires `st.generation <= i`; otherwise, this function fails.
-/
@[expose]
public
def ratchetGetGenerationKey (st: RatchetState Bytes) (i: Nat): Result (RatchetOutput Bytes) :=
  if st.generation = i then
    ratchetGetKey st
  else if i < st.generation then
    Result.internalFailure "ratchet_get_generation_key: generation is in the past"
  else
    match _h: ratchetNextState st with
    | .internalError s => .internalError s
    | .protocolError s => .protocolError s
    | .success nextSt =>
      ratchetGetGenerationKey nextSt i
termination_by i - st.generation
decreasing_by grind [ratchetNextState_generation]

end MLS.TreeDEM
