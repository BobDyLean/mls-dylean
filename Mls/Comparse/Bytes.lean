import Comparse

/-!
`BytesLike` structure for `ByteArray`,
counterpart of `seq_u8_bytes_like` in Comparse (F*).

As in MLS* (`bytes_like_bytes` in `MLS.Test.Utils`), it is not a global instance:
otherwise, in code taking `[CryptoBytes ByteArray]`, two `BytesLike ByteArray` instances
would be in scope (this one and `CryptoBytes.toBytesLike`), and could not be unified.
Code that needs it without `CryptoBytes` installs it with `attribute [local instance] bytesLikeByteArray`.
-/

open Comparse

namespace ByteArray

def splitAt (b : ByteArray) (i : Nat) : Option (ByteArray × ByteArray) :=
  if i ≤ b.size then some (b.extract 0 i, b.extract i b.size) else none

end ByteArray

@[reducible]
def bytesLikeByteArray : BytesLike ByteArray where
  length := ByteArray.size
  empty := .empty
  empty_length := ByteArray.size_empty
  recognizeEmpty b := b.size == 0
  recognizeEmpty_correct b := by grind [ByteArray.size_eq_zero_iff]
  concat := (· ++ ·)
  concat_length _ _ := ByteArray.size_append
  split := ByteArray.splitAt
  split_length b i := by grind [ByteArray.splitAt, ByteArray.size_extract]
  split_concat b1 b2 := by
    grind [ByteArray.splitAt, ByteArray.extract_append_eq_left, ByteArray.extract_append_eq_right]
  concat_split b i := by
    grind [ByteArray.splitAt, ByteArray.extract_append_extract, ByteArray.extract_zero_size]
  toByteArray := some
  fromByteArray := id
  fromByteArray_length _ := rfl
  to_from_ByteArray _ := rfl
  from_to_ByteArray _ := rfl
