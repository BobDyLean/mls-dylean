module

public import MLS.Common.Code.NetworkTypes
public import MLS.Common.Code.Crypto.Derived

/-!
Port of `MLS.Extensions`.

Port-specific differences:
- `find_extension_index` returns a `Nat` (MLS*'s `i:nat{i < List.length extensions}`).
- `set_extension` replaces the extension with `List.set` (MLS* uses `List.Tot.split3`).
- `mk_get_extension` / `mk_set_extension` take a message format (MLS*'s `parser_serializer`).
-/

namespace MLS

open Comparse

variable {Bytes: Type} [BytesLike Bytes]

/-- Port of `find_extension_index`. -/
@[expose]
public
def findExtensionIndex (t: ExtensionType): List (Extension Bytes) → Option Nat
  | [] => none
  | extensionHead::extensionTail =>
    if extensionHead.extensionType = t then
      some 0
    else
      match findExtensionIndex t extensionTail with
      | some res => some (res+1)
      | none => none

/-- Port of `get_extension`. -/
@[expose]
public
def getExtension (t: ExtensionType) (extensions: List (Extension Bytes)): Option Bytes :=
  match findExtensionIndex t extensions with
  | none => none
  | some i => extensions[i]?.map (·.extensionData.val)

/-- Port of `set_extension`. -/
@[expose]
public
def setExtension (t: ExtensionType) (extensions: List (Extension Bytes)) (data: Bytes):
  Result (MlsList (Extension.mf (Bytes := Bytes)))
:= do
  let data ← mkMlsBytes data "set_extension" "data"
  let ext: Extension Bytes := { extensionType := t, extensionData := data }
  let newExtensions :=
    match findExtensionIndex t extensions with
    | none => extensions ++ [ext]
    | some i => extensions.set i ext
  mkMlsList newExtensions "get_extension" "new_extensions"

/-- Port of `empty_extensions`. -/
@[expose]
public
def emptyExtensions: MlsList (Extension.mf (Bytes := Bytes)) :=
  ⟨[], by simp [BytesLike.empty_length, mlsNatPred]⟩

/-- Port of `get_extension_list`. -/
@[expose]
public
def getExtensionList (extensions: List (Extension Bytes)): List ExtensionType :=
  extensions.map (·.extensionType)

/-! ## Helper functions -/

/-- Port of `mk_get_extension`. -/
@[expose]
public
def mkGetExtension {a: Type} (extType: ExtensionType) (mf: NonExtensibleMessageFormat Bytes a)
  (extensions: List (Extension Bytes)): Option a
:=
  match getExtension extType extensions with
  | none => none
  | some res => mf.toExtensible.parse res

/-- Port of `mk_set_extension`. -/
@[expose]
public
def mkSetExtension {a: Type} (extType: ExtensionType) (mf: NonExtensibleMessageFormat Bytes a)
  (extensions: List (Extension Bytes)) (extContent: a): Result (MlsList (Extension.mf (Bytes := Bytes)))
:=
  setExtension extType extensions (serializeNE mf extContent)

end MLS
