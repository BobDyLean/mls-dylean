/-
  Port of `DY.Lib.SplitFunction`: create a global function from several independent local functions
  (the "split function methodology").

  DY* proofs rely on global protocol invariants composed of functions and predicates
  (e.g. what protocol participants are allowed to sign, or how a usage evolves through KDFs).
  Instead of defining them monolithically, each sub-component defines a local function
  for the inputs it owns, identified by a tag (e.g. the tag of a key usage);
  the global function decodes the tag of its input and dispatches to the corresponding local function.
  Proofs then only assume that the global function contains the local functions they need.

  Differences with DY*:
  - Tag sets are lists of tags, and a local function for a tag set `tags` is a `Locals LocalFun tags`:
    a list of local functions tagged with exactly the tags `tags`.
    A local function for a single tag is `Locals.single f`, and `Locals.combine` takes the union of tag sets.
    Since the tags appear in the type, their disjointness is proved by evaluation where the local functions are combined,
    without unfolding their definitions (which may not be exposed).
  - The global function is a plain function `P.Input → P.Output`:
    DY*'s `global_fun_t`, `apply_global_fun`, `mk_global_fun` and `apply_mk_global_fun` (used to curry it) are not needed.
  - Combining is integrated with DyLean's `#combine` macro:
    `HasStep l1 l2` means that `l2` contains the local functions of `l1`.
-/

module

public meta import DY.Meta.CombineMacro
meta import Lean

namespace DySlop.SplitFunction

/-- A local function, tagged with its tag. -/
public
abbrev TaggedLocalFun {Tag: Type} (LocalFun: Tag → Type) := (tag: Tag) × LocalFun tag

section Find

variable {Tag: Type} [DecidableEq Tag] {LocalFun: Tag → Type}

/--
  Port of `find_local_fun`.
  Returns the first local function associated with `tag`, if it exists.
-/
@[expose]
public
def findLocalFun (l: List (TaggedLocalFun LocalFun)) (tag: Tag): Option (TaggedLocalFun LocalFun) :=
  l.find? (·.1 = tag)

/-- Port of `find_local_fun_returns_belonging_tag_set`. -/
theorem fst_of_findLocalFun_eq_some
  (l: List (TaggedLocalFun LocalFun)) (tag: Tag) (x: TaggedLocalFun LocalFun)
  : findLocalFun l tag = some x →
    x.1 = tag
:= by
  intro h
  simpa using List.find?_some h

theorem mem_of_findLocalFun_eq_some
  (l: List (TaggedLocalFun LocalFun)) (tag: Tag) (x: TaggedLocalFun LocalFun)
  : findLocalFun l tag = some x →
    x ∈ l
:=
  List.mem_of_find?_eq_some

theorem findLocalFun_isSome
  (l: List (TaggedLocalFun LocalFun)) (tag: Tag)
  : (findLocalFun l tag).isSome = (tag ∈ l.map (·.1))
:= by
  simp [findLocalFun, List.find?_isSome]

/-- Port of `mk_global_fun_correct_aux`: when tags are unique, `findLocalFun` finds the local function of a tag. -/
theorem findLocalFun_of_mem
  (l: List (TaggedLocalFun LocalFun)) (x: TaggedLocalFun LocalFun)
  : (l.map (·.1)).Nodup →
    x ∈ l →
    findLocalFun l x.1 = some x
:= by
  induction l with
  | nil => simp
  | cons y t ih =>
    intro h_nodup h_mem
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h_nodup
    simp only [findLocalFun, List.find?_cons] at *
    rcases List.mem_cons.mp h_mem with rfl | h_mem <;> split <;> grind

/-- If `l1` is a sublist of `l2` whose tags are unique, they have the same local functions on the tags of `l1`. -/
theorem findLocalFun_of_sublist
  (l1 l2: List (TaggedLocalFun LocalFun)) (tag: Tag)
  : l1.Sublist l2 →
    (l2.map (·.1)).Nodup →
    tag ∈ l1.map (·.1) →
    findLocalFun l2 tag = findLocalFun l1 tag
:= by
  intro h_sub h_nodup h_tag
  obtain ⟨x, h_mem, rfl⟩ := List.mem_map.mp h_tag
  rw [findLocalFun_of_mem l2 x h_nodup (h_sub.subset h_mem)]
  rw [findLocalFun_of_mem l1 x (h_nodup.sublist (h_sub.map _)) h_mem]

end Find

/--
  Port of `split_function_parameters`.

  The global function takes an `Input`, that is decoded into a tag and a `RawInput` for the local functions.
  Differences with DY*: tag sets are lists of tags (see `Locals`), and the global function is a plain function.
-/
public
structure Params where
  Tag: Type
  [decEq: DecidableEq Tag]
  /-- DY*'s `tagged_data_t`. -/
  Input: Type
  /-- DY*'s `raw_data_t`. -/
  RawInput: Type
  Output: Type
  /-- DY*'s `decode_tagged_data`. -/
  decode: Input → Option (Tag × RawInput)
  LocalFun: Tag → Type
  applyLocal: {tag: Tag} → LocalFun tag → RawInput → Output
  /-- DY*'s `default_global_fun`. -/
  default: Input → Output

attribute [instance] Params.decEq

namespace Params

variable (P: Params)

/--
  Port of `mk_global_fun`.
  Given a list of tagged local functions, create the global function.
-/
@[expose]
public
def mkGlobalFun (l: List (TaggedLocalFun P.LocalFun)) (x: P.Input): P.Output :=
  match P.decode x with
  | some (tag, raw) =>
    match findLocalFun l tag with
    | some ⟨_, localFun⟩ => P.applyLocal localFun raw
    | none => P.default x
  | none => P.default x

public
theorem mkGlobalFun_of_findLocalFun
  (l: List (TaggedLocalFun P.LocalFun)) (x: P.Input) {tag: P.Tag} (localFun: P.LocalFun tag) (raw: P.RawInput)
  : P.decode x = some (tag, raw) →
    findLocalFun l tag = some ⟨tag, localFun⟩ →
    P.mkGlobalFun l x = P.applyLocal localFun raw
:= by
  intro h_decode h_find
  simp [mkGlobalFun, h_decode, h_find]

/--
  Port of `mk_global_fun_eq`, as an induction principle:
  a property of the default and the local functions is a property of the global function.
  It is used to lift properties of the local functions to the global function
  (e.g. the function keeps the same output when the trace grows).
-/
public
theorem mkGlobalFun_induction
  (l: List (TaggedLocalFun P.LocalFun)) (x: P.Input) (motive: P.Output → Prop)
  (local_: ∀ tag (localFun: P.LocalFun tag) raw,
    findLocalFun l tag = some ⟨tag, localFun⟩ →
    P.decode x = some (tag, raw) →
    motive (P.applyLocal localFun raw))
  (default: motive (P.default x))
  : motive (P.mkGlobalFun l x)
:= by
  unfold mkGlobalFun
  split
  · rename_i tag raw h_decode
    split
    · rename_i tag' localFun h_find
      obtain rfl := fst_of_findLocalFun_eq_some l tag _ h_find
      exact local_ _ localFun raw h_find h_decode
    · exact default
  · exact default

end Params

section Locals

variable {Tag: Type} {LocalFun: Tag → Type}

/--
  Local functions for the set of tags `tags`
  (DY*'s `dtuple2 tag_set_t local_fun_t` with a list of tags as tag set).
  It is a list of tagged local functions, whose tags are exactly `tags`.
-/
public
structure Locals (LocalFun: Tag → Type) (tags: List Tag) where
  list: List (TaggedLocalFun LocalFun)
  map_fst_list: list.map (·.1) = tags

/-- A local function for a single tag. -/
@[expose]
public
def Locals.single {tag: Tag} (localFun: LocalFun tag): Locals LocalFun [tag] where
  list := [⟨tag, localFun⟩]
  map_fst_list := rfl

/-- The tags of a combination of local functions. -/
@[expose]
public
def Locals.combineTags {n: Nat} (ls: Fin n → (tags: List Tag) × Locals LocalFun tags): List Tag :=
  (List.ofFn (fun id => (ls id).1)).flatten

/-- Combine local functions: the tag set of the result is the union of their tag sets. -/
public
def Locals.combine {n: Nat} (ls: Fin n → (tags: List Tag) × Locals LocalFun tags): Locals LocalFun (Locals.combineTags ls) where
  list := (List.ofFn (fun id => (ls id).2.list)).flatten
  map_fst_list := by
    simp only [List.map_flatten, List.map_ofFn, combineTags]
    congr 1
    apply congrArg List.ofFn
    funext id
    exact (ls id).2.map_fst_list

/-- A property of each local function (e.g. that it stays true when the trace grows). -/
@[expose]
public
def Locals.All {tags: List Tag} (prop: ∀ tag, LocalFun tag → Prop) (l: Locals LocalFun tags): Prop :=
  ∀ x ∈ l.list, prop x.1 x.2

public
theorem Locals.All.single
  {prop: ∀ tag, LocalFun tag → Prop} {tag: Tag} {localFun: LocalFun tag}
  : prop tag localFun →
    (Locals.single localFun).All prop
:= by
  intro h x h_mem
  simp only [Locals.single, List.mem_singleton] at h_mem
  subst h_mem
  exact h

public
theorem Locals.All.combine
  {prop: ∀ tag, LocalFun tag → Prop} {n: Nat} {ls: Fin n → (tags: List Tag) × Locals LocalFun tags}
  : (∀ id, (ls id).2.All prop) →
    (Locals.combine ls).All prop
:= by
  intro h x h_mem
  simp only [Locals.combine, List.mem_flatten, List.mem_ofFn] at h_mem
  obtain ⟨_, ⟨id, rfl⟩, h_mem⟩ := h_mem
  exact h id x h_mem

variable [DecidableEq Tag]

/--
  `l2` contains the local functions of `l1`:
  on the tags of `l1`, `l2` and `l1` find the same local functions.
-/
public
class HasStep {tags1: List Tag} {tags2: semiOutParam (List Tag)} (l1: Locals LocalFun tags1) (l2: semiOutParam (Locals LocalFun tags2)): Prop where
  findLocalFun_eq: ∀ tag ∈ tags1, findLocalFun l2.list tag = findLocalFun l1.list tag

/-- The tags of `l1` are tags of `l2`. -/
public
theorem HasStep.mem_tags
  {tags1 tags2: List Tag} (l1: Locals LocalFun tags1) (l2: Locals LocalFun tags2) [h: HasStep l1 l2]
  (tag: Tag)
  : tag ∈ tags1 →
    tag ∈ tags2
:= by
  intro h_tag
  have h1 := findLocalFun_isSome l1.list tag
  have h2 := findLocalFun_isSome l2.list tag
  rw [l1.map_fst_list] at h1
  rw [l2.map_fst_list] at h2
  grind [h.findLocalFun_eq tag h_tag]

/-- Port of `mk_global_fun_correct` for `Locals.combine`: when tags are unique, a combination contains its components. -/
public
theorem Locals.combine_hasStep
  {n: Nat} (ls: Fin n → (tags: List Tag) × Locals LocalFun tags)
  (h_nodup: (Locals.combineTags ls).Nodup) (id: Fin n)
  : HasStep (ls id).2 (Locals.combine ls)
where
  findLocalFun_eq tag h_tag := by
    have h_map := (Locals.combine ls).map_fst_list
    apply findLocalFun_of_sublist
    · apply List.sublist_flatten_of_mem
      simp only [List.mem_ofFn]
      exact ⟨id, rfl⟩
    · rw [h_map]
      exact h_nodup
    · rw [(ls id).2.map_fst_list]
      exact h_tag

end Locals

namespace Params

variable (P: Params)

/-- The function defined by local functions (the global function when they contain all local functions). -/
public
abbrev Locals.toFun {tags: List P.Tag} (l: Locals P.LocalFun tags): P.Input → P.Output :=
  P.mkGlobalFun l.list

public
theorem Locals.toFun_single
  {tag: P.Tag} (localFun: P.LocalFun tag) (x: P.Input) (raw: P.RawInput)
  : P.decode x = some (tag, raw) →
    Locals.toFun P (Locals.single localFun) x = P.applyLocal localFun raw
:= by
  intro h
  simp [Locals.toFun, mkGlobalFun, Locals.single, findLocalFun, h]

public
theorem Locals.toFun_of_hasStep
  {tags1 tags2: List P.Tag} (l1: Locals P.LocalFun tags1) (l2: Locals P.LocalFun tags2) [h: HasStep l1 l2]
  (x: P.Input) (tag: P.Tag) (raw: P.RawInput)
  : P.decode x = some (tag, raw) →
    tag ∈ tags1 →
    Locals.toFun P l2 x = Locals.toFun P l1 x
:= by
  intro h_decode h_tag
  simp [Locals.toFun, mkGlobalFun, h_decode, h.findLocalFun_eq tag h_tag]

/--
  The local function for the tag `tag` applied to `raw`, or `default` if there is none
  (DY*'s `params.apply_local_fun local_fun raw_data`, where `local_fun` is found in a list of local functions).
-/
@[expose]
public
def Locals.apply {tags: List P.Tag} (l: Locals P.LocalFun tags) (tag: P.Tag) (raw: P.RawInput) (default: P.Output): P.Output :=
  match findLocalFun l.list tag with
  | some ⟨_, localFun⟩ => P.applyLocal localFun raw
  | none => default

/-- Port of `mk_global_fun_eq`. -/
public
theorem Locals.toFun_eq
  {tags: List P.Tag} (l: Locals P.LocalFun tags) (x: P.Input) (tag: P.Tag) (raw: P.RawInput)
  : P.decode x = some (tag, raw) →
    Locals.toFun P l x = Locals.apply P l tag raw (P.default x)
:= by
  intro h
  simp [Locals.toFun, mkGlobalFun, Locals.apply, h]

public
theorem Locals.toFun_eq_default
  {tags: List P.Tag} (l: Locals P.LocalFun tags) (x: P.Input)
  : P.decode x = none →
    Locals.toFun P l x = P.default x
:= by
  intro h
  simp [Locals.toFun, mkGlobalFun, h]

public
theorem Locals.apply_single
  {tag: P.Tag} (localFun: P.LocalFun tag) (raw: P.RawInput) (default: P.Output)
  : Locals.apply P (Locals.single localFun) tag raw default = P.applyLocal localFun raw
:= by
  simp [Locals.apply, Locals.single, findLocalFun]

theorem Locals.apply_of_hasStep
  {tags1 tags2: List P.Tag} (l1: Locals P.LocalFun tags1) (l2: Locals P.LocalFun tags2) [h: HasStep l1 l2]
  (tag: P.Tag) (raw: P.RawInput) (default: P.Output)
  : tag ∈ tags1 →
    Locals.apply P l2 tag raw default = Locals.apply P l1 tag raw default
:= by
  intro h_tag
  simp [Locals.apply, h.findLocalFun_eq tag h_tag]

/--
  A relation between the local functions on two inputs is a relation between their applications
  (e.g. a local predicate stays true when the trace grows).
-/
public
theorem Locals.apply_rel
  {tags: List P.Tag} (l: Locals P.LocalFun tags) (tag: P.Tag) (raw1 raw2: P.RawInput) (default1 default2: P.Output)
  (R: P.Output → P.Output → Prop)
  (local_: ∀ x ∈ l.list, R (P.applyLocal x.2 raw1) (P.applyLocal x.2 raw2))
  (default: R default1 default2)
  : R (Locals.apply P l tag raw1 default1) (Locals.apply P l tag raw2 default2)
:= by
  unfold Locals.apply
  split
  · rename_i h_find
    exact local_ _ (mem_of_findLocalFun_eq_some _ _ _ h_find)
  · exact default

/-- Port of `has_local_fun`: the function `g` coincides with the local functions `l` on their tags. -/
@[expose]
public
def HasLocal (g: P.Input → P.Output) {tags: List P.Tag} (l: Locals P.LocalFun tags): Prop :=
  ∀ x tag raw,
    P.decode x = some (tag, raw) →
    tag ∈ tags →
    g x = Locals.apply P l tag raw (P.default x)

/-- Port of `mk_global_fun_correct`. -/
public
theorem Locals.toFun_hasLocal {tags: List P.Tag} (l: Locals P.LocalFun tags): P.HasLocal (Locals.toFun P l) l :=
  fun x tag raw h_decode _ => Locals.toFun_eq P l x tag raw h_decode

public
theorem HasLocal.of_hasStep
  (g: P.Input → P.Output) {tags1 tags2: List P.Tag} (l1: Locals P.LocalFun tags1) (l2: Locals P.LocalFun tags2) [HasStep l1 l2]
  : P.HasLocal g l2 →
    P.HasLocal g l1
:= by
  intro h x tag raw h_decode h_tag
  rw [h x tag raw h_decode (HasStep.mem_tags l1 l2 tag h_tag)]
  exact Locals.apply_of_hasStep P l1 l2 tag raw _ h_tag

end Params

end DySlop.SplitFunction

/-
  Support for the `#combine` macro.

  For a split function whose local functions for the tags `tags` have type `LocalType tags`,
  `#combine into foo from A, B` defines
  - `foo.internal`, the sources `A.foo` and `B.foo` with their tags,
  - `foo: LocalType (Locals.combineTags foo.internal)`, their combination,
  - `foo.nodup`, the proof (by `decide`) that their tags are disjoint,
  - `HasStep A.foo foo` and `HasStep B.foo foo`,
  - with `+toplevel`, the global instance (e.g. `instance: SignPred := SignPred.ofLocal foo`) and its `Has` instance.
  Proofs about local functions (e.g. `SignPred.LocalProof`) are combined similarly.
-/

namespace DySlop.SplitFunction.Combine

open Lean DY.Meta.CombineMacro

public meta
structure Config where
  /-- e.g. `signPred` -/
  name: Name
  /-- e.g. `DySlop.Signature.SignPred.Local` -/
  localTypeName: Name
  /-- e.g. `String` -/
  tagTypeName: Name := ``String
  /-- The commands generated with `+toplevel`, given the combination (e.g. `signPred`). -/
  mkTopLevel: Ident → MacroM (Array Command)

/--
  The usual top-level commands: the global instance (e.g. `instance: SignPred := SignPred.ofLocal signPred`)
  and its `Has` instance (e.g. `instance: SignPred.Has signPred := SignPred.ofLocal_has signPred`).
-/
public meta
def globalInstances (globalClassName ofLocalName hasClassName ofLocalHasName: Name) (nameStx: Ident): MacroM (Array Command) := do
  let globalClassStx := mkIdent globalClassName
  let ofLocalStx := mkIdent ofLocalName
  let hasClassStx := mkIdent hasClassName
  let ofLocalHasStx := mkIdent ofLocalHasName
  return #[
    ← `(command| public instance: $globalClassStx := $ofLocalStx $nameStx),
    ← `(command| public instance: $hasClassStx $nameStx := $ofLocalHasStx $nameStx)
  ]

meta
def matchArms (sources: TSyntaxArray `combine_from) (mkArm: Ident → TSyntaxArray `term → MacroM Term): MacroM (Array (TSyntax ``Parser.Term.matchAlt)) := do
  let mut arms := #[]
  for i in [:sources.size] do
    let `(combine_from| $nameSource:ident $argsSource* ) := sources[i]! | Macro.throwUnsupported
    let arm ← `(Parser.Term.matchAltExpr| | $(quote i) => $(← mkArm nameSource argsSource))
    arms := arms.push arm
  -- workaround for https://github.com/leanprover/lean4/issues/9292
  arms := arms.push (← `(Parser.Term.matchAltExpr| | ⟨ _+$(quote sources.size), _ ⟩ => False.elim (by grind)))
  return arms

meta
def sourceIdent (nameSource: Ident) (name: Name): Ident :=
  mkIdentFrom nameSource <| nameSource.getId.modifyBase (· ++ name)

public meta
def mkCombine
  (toplevel: Bool) (params: TSyntaxArray ``Parser.Term.bracketedBinder) (sources: TSyntaxArray `combine_from)
  (config: Config)
  : MacroM (Array Command)
:= do
  let args := params.flatMap explicitNameOfBracketedBinder
  let nSources: Term := quote sources.size
  let nameStx := mkIdent config.name
  let internalStx := mkIdent (config.name ++ `internal)
  let nodupStx := mkIdent (config.name ++ `nodup)
  let localTypeStx := mkIdent config.localTypeName
  let tagTypeStx := mkIdent config.tagTypeName

  let arms ← matchArms sources fun nameSource argsSource =>
    `(term| ⟨_, $(sourceIdent nameSource config.name) $argsSource*⟩)
  let internalCmd ← `(command|
    public
    def $internalStx $params*: Fin $nSources → (tags: List $tagTypeStx) × $localTypeStx tags := fun $arms:matchAlt*
  )
  let combineCmd ← `(command|
    public
    def $nameStx $params*: $localTypeStx (DySlop.SplitFunction.Locals.combineTags ($internalStx $args*)) :=
      DySlop.SplitFunction.Locals.combine ($internalStx $args*)
  )
  let nodupCmd ← `(command|
    public
    theorem $nodupStx $params*: (DySlop.SplitFunction.Locals.combineTags ($internalStx $args*)).Nodup := by
      first
      | exact of_decide_eq_true rfl
      | fail "#combine: the combined local functions must have disjoint tags"
  )
  let mut hasStepCmds := #[]
  for i in [:sources.size] do
    let `(combine_from| $nameSource:ident $argsSource* ) := sources[i]! | Macro.throwUnsupported
    let freshInstanceName ← withFreshMacroScope `(declId| inst)
    let cmd ← `(command|
      public
      instance (priority := default) $freshInstanceName $params*:
        DySlop.SplitFunction.HasStep ($(sourceIdent nameSource config.name) $argsSource*) ($nameStx $args*)
      :=
        DySlop.SplitFunction.Locals.combine_hasStep ($internalStx $args*) ($nodupStx $args*) $(quote i)
    )
    hasStepCmds := hasStepCmds.push cmd

  let topLevel ← if toplevel then config.mkTopLevel nameStx else pure #[]

  return #[internalCmd, combineCmd, nodupCmd] ++ hasStepCmds ++ topLevel

public meta
structure ProofConfig where
  /-- e.g. `signPredProof` -/
  name: Name
  /-- e.g. `signPred` -/
  refereeName: Name
  /-- e.g. `DySlop.Signature.SignPred.LocalProof` -/
  localProofName: Name
  /-- e.g. `DySlop.Signature.SignPred.LocalProof.combine` -/
  combineName: Name
  /-- The commands generated with `+toplevel`, given the combination (e.g. `signPredProof`). -/
  mkTopLevel: Ident → MacroM (Array Command)

/-- The usual top-level command: the global proof instance (e.g. `instance: SignPredProof := SignPred.LocalProof.toGlobal signPredProof`). -/
public meta
def globalProofInstance (globalClassName toGlobalName: Name) (nameStx: Ident): MacroM (Array Command) := do
  let globalClassStx := mkIdent globalClassName
  let toGlobalStx := mkIdent toGlobalName
  return #[← `(command| public instance: $globalClassStx := $toGlobalStx $nameStx)]

public meta
def mkProofCombine
  (toplevel: Bool) (params: TSyntaxArray ``Parser.Term.bracketedBinder) (sources: TSyntaxArray `combine_from)
  (config: ProofConfig)
  : MacroM (Array Command)
:= do
  let args := params.flatMap explicitNameOfBracketedBinder
  let nSources: Term := quote sources.size
  let nameStx := mkIdent config.name
  let internalStx := mkIdent (config.name ++ `internal)
  let refereeStx := mkIdent config.refereeName
  let refereeInternalStx := mkIdent (config.refereeName ++ `internal)
  let localProofStx := mkIdent config.localProofName
  let combineStx := mkIdent config.combineName

  let arms ← matchArms sources fun nameSource argsSource =>
    `(term| $(sourceIdent nameSource config.name) $argsSource*)
  let internalCmd ← `(command|
    public
    theorem $internalStx $params*: (id: Fin $nSources) → $localProofStx ($refereeInternalStx $args* id).2 := fun $arms:matchAlt*
  )
  let combineCmd ← `(command|
    public
    theorem $nameStx $params*: $localProofStx ($refereeStx $args*) :=
      $combineStx ($refereeInternalStx $args*) ($internalStx $args*)
  )

  let topLevel ← if toplevel then config.mkTopLevel nameStx else pure #[]

  return #[internalCmd, combineCmd] ++ topLevel

end DySlop.SplitFunction.Combine
