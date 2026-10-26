module

public import MLS.Common.Code.Crypto.Derived
public import MLS.TreeKEM.Code.NetworkTypes

/-!
Port of `MLS.TreeKEM.PSK`.
-/

namespace MLS.TreeKEM

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/--
Port of `compute_psk_secret_step`.
Compute psk_secret[i+1] given psk[i], psk_label[i] and psk_secret[i]
-/
@[expose]
public
def computePskSecretStep (label: PskLabel Bytes) (psk: Bytes) (prevPskSecret: Bytes): Result Bytes := do
  let pskExtracted ← CryptoBytes.kdfExtract zeroVector psk
  let pskInput ← expandWithLabel pskExtracted "derived psk" (serializeNE PskLabel.mf label) (CryptoBytes.kdfLength Bytes)
  let newPskSecret ← CryptoBytes.kdfExtract pskInput prevPskSecret
  pure newPskSecret

/--
Port of `compute_psk_secret_aux`.
Compute psk_secret[n] given psk_secret[ind]
MLS* requires `ind <= List.Tot.length l`; otherwise, this function returns `pskSecretInd`.
-/
@[expose]
public
def computePskSecretAux (l: List (PreSharedKeyId Bytes × Bytes)) (ind: Nat) (pskSecretInd: Bytes): Result Bytes :=
  if h: ind < l.length then do
    let (id, psk) := l[ind]
    let index ← mkUInt16 ind "compute_psk_secret_aux" "index"
    let count ← mkUInt16 l.length "compute_psk_secret_aux" "index"
    let label := { id, index, count }
    let nextPskSecret ← computePskSecretStep label psk pskSecretInd
    computePskSecretAux l (ind+1) nextPskSecret
  else
    pure pskSecretInd
termination_by l.length - ind

/-- Port of `compute_psk_secret`. -/
@[expose]
public
def computePskSecret (l: List (PreSharedKeyId Bytes × Bytes)): Result Bytes :=
  computePskSecretAux l 0 zeroVector

end MLS.TreeKEM
