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
  - As DyLean's state invariants (`PersistentLocalState.CompromisableLocalStateInv`), the map predicate
    is a class, `MapPred K V` (one per map type), which gives the invariant of maps (`MapPred.instInv`,
    DY*'s `map_session_invariant`); DY*'s `has_map_session_invariant mpred` is the instance `MapPred K V`.
  - The map predicate has no session identifier, and the knowability of keys and values
    (`pred_knowable`) is stated for the label of any map containing them
    (in DyLean, the label of a state is the compromise of this very state).
  - `find_value_same_trace` is not ported (DyLean's Hoare triples do not state that the trace is unchanged).
-/

module

public import DY.Comparse
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

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

/-! ## Map invariants -/

section Invariants

open PersistentLocalState

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesInvariants] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesInvariants.Has Literal.invariants]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Concat.invariants]

/--
  Port of `map_predicate`: the predicate relating a key and its associated value, in the maps of type `Map K V`.
  The key and the value must be knowable by the label of any map of the principal containing them.
-/
public
class MapPred (K V: Type) [MapTypes K V] [ExecTraceTypes.Has (Compromise.ExecEntryT (Map K V))] where
  pred: ProofTrace → Participant → K → V → Prop
  pred_later: ∀ tr1 tr2 prin key value, tr1 ≤ tr2 → pred tr1 prin key value → pred tr2 prin key value
  pred_knowable: ∀ tr prin key value (m: Map K V), { key, value } ∈ m.keyValues → pred tr prin key value →
    (MapTypes.mfKey (V := V)).wf (Bytes.KnowableBy (label prin m) · tr) key ∧
    (MapTypes.mfValue (K := K)).wf (Bytes.KnowableBy (label prin m) · tr) value

grind_pattern MapPred.pred_later => tr1 ≤ tr2, MapPred.pred tr1 prin key value
grind_pattern [grind_later] MapPred.pred_later => tr1 ≤ tr2, MapPred.pred tr1 prin key value

variable {K V: Type} [MapTypes K V] [ExecTraceTypes.Has (Compromise.ExecEntryT (Map K V))] [MapPred K V]

/-- Port of `map_invariant` (with `map_elem_invariant`). -/
@[expose]
public
def MapPred.Invariant (tr: ProofTrace) (prin: Participant) (m: Map K V): Prop :=
  ∀ x ∈ m.keyValues, MapPred.pred tr prin x.key x.value

/-- Port of `map_session_invariant`: the invariant of the maps of type `Map K V`. -/
public
instance MapPred.instInv: CompromisableLocalStateInv (Map K V) where
  invariant prin m tr := MapPred.Invariant tr prin m
  invariant_later prin m tr1 tr2 := by
    grind [MapPred.Invariant]
  invariant_implies_KnowableBy prin m tr h := by
    simp only [IsWellFormed, ParseableSerializeable.mf, MapElem.mf]
    simp only [Comparse.ExtensibleMessageFormat.isomorphic.wf_eq, Comparse.ExtensibleMessageFormat.list.wf_eq,
      Comparse.NonExtensibleMessageFormat.isomorphic.wf_eq, Comparse.NonExtensibleMessageFormat.prod.wf_eq, MapElem.g, Map.g]
    intro ⟨key, value⟩ hmem
    exact MapPred.pred_knowable tr prin key value m hmem (h _ hmem)

end Invariants

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

/-! ## Map API proofs -/

section FindValueAux

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable {K V: Type} [MapTypes K V]

/-- Port of the postcondition of `find_value_aux`. -/
theorem mem_of_findValueAux (key: K) (l: List (MapElem K V)) (value: V):
  findValueAux key l = some value → { key, value } ∈ l
:= by
  have hinj: Function.Injective (MapTypes.mfKey (K := K) (V := V)).toExtensible.serialize := by
    intro x y h
    have := congrArg (MapTypes.mfKey (K := K) (V := V)).toExtensible.parse h
    simp only [Comparse.ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv] at this
    grind
  induction l with
  | nil => simp [findValueAux]
  | cons h t ih =>
    obtain ⟨hkey, hvalue⟩ := h
    simp only [findValueAux]
    split
    · have := hinj ‹_›
      grind
    · grind

end FindValueAux

section Proofs

open PersistentLocalState

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable {K V: Type} [MapTypes K V] [ExecTraceTypes.Has (Compromise.ExecEntryT (Map K V))] [MapPred K V]
variable [ExecTraceTypes.Has (State.ExecEntryT (Map K V))]
variable [ProofTraceTypes.Has (State.ProofEntryT (Map K V))] [TraceInvariant.Has (State.ProofEntryT (Map K V))]

/-- Port of `initialize_map_invariant`. -/
@[instance]
public
theorem initializeMap.proof (prin: Participant):
  HoareTriple
    (initializeMap K V prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeMap
  step by
    simp [LocalStateInv.invariant, MapPred.Invariant]
  trivial

/-- Port of `add_key_value_invariant`. -/
@[instance]
public
theorem addKeyValue.proof (prin: Participant) (handle: Nat) (key: K) (value: V):
  HoareTriple
    (addKeyValue prin handle key value)
    (fun tr => MapPred.pred tr prin key value)
    (fun _ _ => True)
:= by
  unfold addKeyValue
  step
  step_intro
  step by
    simp only [LocalStateInv.invariant] at *
    grind [MapPred.Invariant]
  trivial

/-- Port of `find_value_invariant`. -/
@[instance]
public
theorem findValue.proof (prin: Participant) (handle: Nat) (key: K):
  HoareTriple
    (findValue prin handle key: Traceful V)
    (fun _ => True)
    (fun value tr => MapPred.pred tr prin key value)
:= by
  unfold findValue
  step
  split
  · step
    have := mem_of_findValueAux key _ _ ‹_›
    simp only [LocalStateInv.invariant] at *
    grind [MapPred.Invariant]
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

end Proofs

end DySlop.Map
