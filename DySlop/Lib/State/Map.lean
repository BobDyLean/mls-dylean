/-
  Port of `DY.Lib.State.Map`: a generic state for maps (association lists),
  useful when specifying a protocol.

  Differences with DY*:
  - DY* has a single state trace entry, and DY*'s `map` is a local state with a tag (`map_types`'s `tag`);
    DyLean has one trace entry per state type: a map is a (compromisable) local state of type `Map K V`,
    and `MapTypes` has no tag.
    The protocol includes `PersistentLocalState.CompromisableState.ExecEntryT (Map K V)` in its trace.
  - DyLean's states are immutable and identified by handles (the timestamp at which they were stored),
    instead of DY*'s session identifiers:
    `initializeMap` returns the handle of the new map, and `addKeyValue` stores a new version of the map,
    and returns its handle.
  - `find_value` fails when the key is not found (`Traceful` already supports failure).
  - DY* requires keys to have a decidable equality (`eqtype`);
    here, keys are compared by their serialization, which is equivalent since their format is non-ambiguous.
  - The invariants (`map_predicate`, `map_session_invariant`) and their lemmas are not ported yet.
-/

module

public import DY.Comparse
public import DY.Actions.PersistentLocalState

open DY DY.Comparse

namespace DySlop.Map

section Types

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

/--
  Port of `map_types`.
  The parameters necessary to define the map functions: the formats of keys and values.
  Unlike DY*, there is no tag: maps are distinguished by their types.
-/
public
class MapTypes (K V: Type) where
  mfKey: Comparse.NonExtensibleMessageFormat Bytes K
  mfValue: Comparse.NonExtensibleMessageFormat Bytes V
  [mfKey_na: mfKey.IsNonAmbiguous]
  [mfKey_ur: mfKey.HasUniqueRepresentation]
  [mfKey_pc: mfKey.ParseConsumes]
  [mfValue_na: mfValue.IsNonAmbiguous]
  [mfValue_ur: mfValue.HasUniqueRepresentation]

attribute [instance] MapTypes.mfKey_na MapTypes.mfKey_ur MapTypes.mfKey_pc
attribute [instance] MapTypes.mfValue_na MapTypes.mfValue_ur

end Types

/-- Port of `map_elem`. -/
public
structure MapElem (K V: Type) where
  key: K
  value: V

/-- Port of `map`. -/
public
structure Map (K V: Type) where
  keyValues: List (MapElem K V)

section Formats

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable {K V: Type} [MapTypes K V]

namespace MapElem

public
def f: K × V → MapElem K V :=
  fun (key, value) => { key, value }

public
def g: MapElem K V → K × V :=
  fun { key, value } => (key, value)

public
instance: Comparse.LeftInverse (g (K := K) (V := V)) f := ⟨by intro _; rfl⟩
public
instance: Comparse.RightInverse (g (K := K) (V := V)) f := ⟨by intro _; rfl⟩

end MapElem

/-- Port of `ps_map_elem`. -/
public
def MapElem.mf: Comparse.NonExtensibleMessageFormat Bytes (MapElem K V) :=
  .isomorphic (.prod (MapTypes.mfKey (K := K) (V := V)) (MapTypes.mfValue (K := K) (V := V))) MapElem.f MapElem.g

public
instance: (MapElem.mf (K := K) (V := V)).IsNonAmbiguous := by
  dsimp only [MapElem.mf]; infer_instance

public
instance: (MapElem.mf (K := K) (V := V)).HasUniqueRepresentation := by
  dsimp only [MapElem.mf]; infer_instance

public
instance: (MapElem.mf (K := K) (V := V)).ParseConsumes := by
  dsimp only [MapElem.mf]; infer_instance

namespace Map

public
def f: List (MapElem K V) → Map K V :=
  fun l => { keyValues := l }

public
def g: Map K V → List (MapElem K V) :=
  fun m => m.keyValues

public
instance: Comparse.LeftInverse (g (K := K) (V := V)) f := ⟨by intro _; rfl⟩
public
instance: Comparse.RightInverse (g (K := K) (V := V)) f := ⟨by intro _; rfl⟩

end Map

/-- Port of `ps_map` (and of `local_state_map`, for its format). -/
public
instance Map.ps: ParseableSerializeable (Map K V) := .make <|
  .isomorphic (.list MapElem.mf) Map.f Map.g

end Formats

/-! ## Map API -/

section API

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [ExecTraceTypes]

/-- Port of `initialize_map`. Stores an empty map, and returns its handle. -/
public
def initializeMap (K V: Type) [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map K V))]
  (prin: Participant): Traceful Nat
:=
  PersistentLocalState.storeLocalState prin ({ keyValues := [] }: Map K V)

variable {K V: Type} [MapTypes K V] [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map K V))]

/--
  Port of `add_key_value`.
  Stores a new version of the map at `handle`, with the new key-value pair, and returns its handle.
-/
public
def addKeyValue (prin: Participant) (handle: Nat) (key: K) (value: V): Traceful Nat := do
  let theMap: Map K V ← PersistentLocalState.getLocalState prin handle
  let newElem: MapElem K V := { key, value }
  PersistentLocalState.storeLocalState prin ({ keyValues := newElem :: theMap.keyValues }: Map K V)

/--
  Port of `find_value_aux`.
  Keys are compared by their serialization.
-/
public
def findValueAux (key: K): List (MapElem K V) → Option V
  | [] => none
  | h :: t =>
    let serializeKey := (MapTypes.mfKey (K := K) (V := V)).toExtensible.serialize
    if serializeKey h.key = serializeKey key then
      some h.value
    else
      findValueAux key t

/--
  Port of `find_value`.
  Fails when the key is not in the map.
-/
public
def findValue (prin: Participant) (handle: Nat) (key: K): Traceful V := do
  let theMap: Map K V ← PersistentLocalState.getLocalState prin handle
  match findValueAux key theMap.keyValues with
  | some value => pure value
  | none => failure

end API

end DySlop.Map
