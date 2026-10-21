/-!
Authenticated encryption with associated data.
The tag is appended to the ciphertext.
-/

namespace OpenSSL.AEAD

inductive Algorithm where
  | aes128Gcm
  | aes256Gcm
  | chacha20Poly1305
deriving DecidableEq, Repr

/-- OpenSSL name of the algorithm. -/
def Algorithm.name: Algorithm → String
  | .aes128Gcm => "AES-128-GCM"
  | .aes256Gcm => "AES-256-GCM"
  | .chacha20Poly1305 => "ChaCha20-Poly1305"

def Algorithm.keyLength: Algorithm → Nat
  | .aes128Gcm => 16
  | .aes256Gcm => 32
  | .chacha20Poly1305 => 32

def Algorithm.nonceLength (_: Algorithm): Nat := 12

def Algorithm.tagLength (_: Algorithm): Nat := 16

@[extern "lean_openssl_aead_encrypt"]
opaque encryptRaw (cipher: @& String) (tagLen: USize) (key nonce ad plaintext: @& ByteArray): Option ByteArray

@[extern "lean_openssl_aead_decrypt"]
opaque decryptRaw (cipher: @& String) (tagLen: USize) (key nonce ad ciphertext: @& ByteArray): Option ByteArray

def encrypt (a: Algorithm) (key nonce ad plaintext: ByteArray): Option ByteArray :=
  if nonce.size == a.nonceLength then encryptRaw a.name a.tagLength.toUSize key nonce ad plaintext else none

def decrypt (a: Algorithm) (key nonce ad ciphertext: ByteArray): Option ByteArray :=
  if nonce.size == a.nonceLength then decryptRaw a.name a.tagLength.toUSize key nonce ad ciphertext else none

end OpenSSL.AEAD
