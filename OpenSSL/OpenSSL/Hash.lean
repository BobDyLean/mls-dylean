module

/-!
Hash functions, HMAC (RFC 2104) and HKDF (RFC 5869).
-/

namespace OpenSSL.Hash

public
inductive Algorithm where
  | sha2_256
  | sha2_384
  | sha2_512
deriving DecidableEq, Repr

/-- OpenSSL name of the algorithm. -/
@[expose]
public
def Algorithm.name: Algorithm → String
  | .sha2_256 => "SHA256"
  | .sha2_384 => "SHA384"
  | .sha2_512 => "SHA512"

@[expose]
public
def Algorithm.hashLength: Algorithm → Nat
  | .sha2_256 => 32
  | .sha2_384 => 48
  | .sha2_512 => 64

@[extern "lean_openssl_digest"]
public
opaque digestRaw (name: @& String) (msg: @& ByteArray): Option ByteArray

@[extern "lean_openssl_hmac"]
public
opaque hmacRaw (digest: @& String) (key: @& ByteArray) (data: @& ByteArray): Option ByteArray

@[extern "lean_openssl_hkdf_extract"]
public
opaque hkdfExtractRaw (digest: @& String) (salt: @& ByteArray) (ikm: @& ByteArray) (len: USize): Option ByteArray

@[extern "lean_openssl_hkdf_expand"]
public
opaque hkdfExpandRaw (digest: @& String) (prk: @& ByteArray) (info: @& ByteArray) (len: USize): Option ByteArray

@[expose]
public
def hash (a: Algorithm) (msg: ByteArray): Option ByteArray :=
  digestRaw a.name msg

@[expose]
public
def hmac (a: Algorithm) (key data: ByteArray): Option ByteArray :=
  hmacRaw a.name key data

/-- `HKDF-Extract(salt, ikm)`. -/
@[expose]
public
def hkdfExtract (a: Algorithm) (salt ikm: ByteArray): Option ByteArray :=
  hkdfExtractRaw a.name salt ikm a.hashLength.toUSize

/-- `HKDF-Expand(prk, info, len)`. -/
@[expose]
public
def hkdfExpand (a: Algorithm) (prk info: ByteArray) (len: Nat): Option ByteArray :=
  if len ≤ 255 * a.hashLength then hkdfExpandRaw a.name prk info len.toUSize else none

end OpenSSL.Hash
