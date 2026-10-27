/-
  Definitions shared by the DY* equational theories:
  usages, and the generic predicates and lemmas of `DY.Core.Bytes`
  that are not already provided by DyLean.

  DY*'s `usage` is an inductive type, whereas DyLean's `Usage` is a structure
  `{ type, tag, data }`. Each DY* usage constructor `C tag data` becomes the usage
  `Usage.c tag data = { type := "C", tag, data := some data }`,
  and DY*'s discriminator `C? usg` becomes `usg.type = "C"`
  (as in DyLean, e.g. `skUsg.type = "SigKey"`).
  DY*'s `NoUsage` is DyLean's `Usage.nothing`.
  The KEM usages `KemKey usg` and `KemNonce usg` contain a usage:
  they are `usg` with its type prefixed by `"KemKey/"` (resp. `"KemNonce/"`),
  e.g. `Usage.kemKey (Usage.aeadKey tag data) = { type := "KemKey/AeadKey", tag, data := some data }`.
  These encodings are injective, and `Usage.kemNonce?` decodes `KemNonce`.
-/

module

public import DY.Bytes
public import DY.Trace

namespace DY

section Strings

/-- `s` without its prefix `p`, if `s` starts with `p`. -/
@[expose]
public
def stripPrefix? (p s: String): Option String :=
  let rest := String.ofList (s.toList.drop p.length)
  if p ++ rest = s then some rest else none

public
theorem stripPrefix?_append (p s: String): stripPrefix? p (p ++ s) = some s := by
  have: String.ofList ((p ++ s).toList.drop p.length) = s := by
    rw [String.toList_append, ← String.length_toList, List.drop_left]
    simp
  simp only [stripPrefix?, this, ite_true]

theorem eq_of_stripPrefix? (p s r: String): stripPrefix? p s = some r → s = p ++ r := by
  simp only [stripPrefix?]
  split
  · rintro ⟨⟩
    grind
  · simp

theorem append_left_injective (p: String): Function.Injective (p ++ ·) := by
  intro a b h
  have := congrArg String.toList h
  simp only [String.toList_append, List.append_cancel_left_eq] at this
  exact String.toList_inj.mp this

end Strings

section Usages

variable [BytesFunctor]

/-- Port of `SigKey`. -/
@[expose]
public
def Usage.sigKey (tag: String) (data: Bytes): Usage where
  type := "SigKey"
  tag := tag
  data := some data

/-- Port of `SigNonce`. -/
@[expose]
public
def Usage.sigNonce: Usage where
  type := "SigNonce"
  tag := ""
  data := none

/-- Port of `PkeKey`. -/
@[expose]
public
def Usage.pkeKey (tag: String) (data: Bytes): Usage where
  type := "PkeKey"
  tag := tag
  data := some data

/-- Port of `PkeNonce`. -/
@[expose]
public
def Usage.pkeNonce: Usage where
  type := "PkeNonce"
  tag := ""
  data := none

/-- Port of `AeadKey`. -/
@[expose]
public
def Usage.aeadKey (tag: String) (data: Bytes): Usage where
  type := "AeadKey"
  tag := tag
  data := some data

/-- Port of `DhKey`. -/
@[expose]
public
def Usage.dhKey (tag: String) (data: Bytes): Usage where
  type := "DhKey"
  tag := tag
  data := some data

/-- Port of `KdfExpandKey`. -/
@[expose]
public
def Usage.kdfExpandKey (tag: String) (data: Bytes): Usage where
  type := "KdfExpandKey"
  tag := tag
  data := some data

/-- Port of `MacKey`. -/
@[expose]
public
def Usage.macKey (tag: String) (data: Bytes): Usage where
  type := "MacKey"
  tag := tag
  data := some data

/-- Port of `KemKey`. -/
@[expose]
public
def Usage.kemKey (usg: Usage): Usage :=
  { usg with type := "KemKey/" ++ usg.type }

/-- Port of `KemNonce`. -/
@[expose]
public
def Usage.kemNonce (usg: Usage): Usage :=
  { usg with type := "KemNonce/" ++ usg.type }

/-- Inverse of `Usage.kemNonce` (DY*'s `match usg with KemNonce usg -> Some usg | _ -> None`). -/
@[expose]
public
def Usage.kemNonce? (usg: Usage): Option Usage :=
  (stripPrefix? "KemNonce/" usg.type).map ({ usg with type := · })

@[simp]
public
theorem Usage.type_kemKey (usg: Usage): (Usage.kemKey usg).type = "KemKey/" ++ usg.type := rfl

@[simp]
public
theorem Usage.type_kemNonce (usg: Usage): (Usage.kemNonce usg).type = "KemNonce/" ++ usg.type := rfl

@[grind inj]
public
theorem Usage.kemKey_injective: Function.Injective Usage.kemKey := by
  intro ⟨t1, tag1, d1⟩ ⟨t2, tag2, d2⟩ h
  simp only [Usage.kemKey, Usage.mk.injEq] at h
  have := append_left_injective "KemKey/" h.1
  grind

@[grind inj]
public
theorem Usage.kemNonce_injective: Function.Injective Usage.kemNonce := by
  intro ⟨t1, tag1, d1⟩ ⟨t2, tag2, d2⟩ h
  simp only [Usage.kemNonce, Usage.mk.injEq] at h
  have := append_left_injective "KemNonce/" h.1
  grind

@[simp]
public
theorem Usage.kemNonce?_kemNonce (usg: Usage): (Usage.kemNonce usg).kemNonce? = some usg := by
  simp [Usage.kemNonce?, Usage.kemNonce, stripPrefix?_append]

grind_pattern Usage.kemNonce?_kemNonce => (Usage.kemNonce usg).kemNonce?

public
theorem Usage.eq_kemNonce_of_kemNonce? (usg usg': Usage)
  : usg.kemNonce? = some usg' →
    usg = Usage.kemNonce usg'
:= by
  obtain ⟨t, tag, d⟩ := usg
  simp only [Usage.kemNonce?, Option.map_eq_some_iff, Usage.kemNonce]
  rintro ⟨r, h, rfl⟩
  have := eq_of_stripPrefix? _ _ _ h
  grind

grind_pattern Usage.eq_kemNonce_of_kemNonce? => usg.kemNonce?, some usg'

/--
  The type of a `KemKey` usage starts with `"KemKey/"`,
  hence differs from e.g. `"AeadKey"` (the hypothesis is then proved by `decide`).
-/
public
theorem Usage.type_kemKey_ne (usg: Usage) (t: String)
  : "KemKey/".toList.isPrefixOf t.toList = false →
    (Usage.kemKey usg).type ≠ t
:= by
  intro h heq
  subst heq
  simp [String.toList_append] at h

/-- Same as `Usage.type_kemKey_ne`, for `KemNonce` usages. -/
public
theorem Usage.type_kemNonce_ne (usg: Usage) (t: String)
  : "KemNonce/".toList.isPrefixOf t.toList = false →
    (Usage.kemNonce usg).type ≠ t
:= by
  intro h heq
  subst heq
  simp [String.toList_append] at h

public
theorem Usage.kemKey_ne_kemNonce (usg1 usg2: Usage): Usage.kemKey usg1 ≠ Usage.kemNonce usg2 := by
  intro h
  have := congrArg (String.toList ∘ Usage.type) h
  simp [String.toList_append] at this

end Usages

section Predicates

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `mk_has_xxx_usage_inj`. -/
public
theorem Bytes.XXXHasUsage_inj
  [GetUsage] [GetLabel]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (usg1 usg2: Usage) (tr: ProofTrace)
  : b.XXXHasUsage extract usg1 tr →
    b.XXXHasUsage extract usg2 tr →
    (usg1 = usg2 ∨ (b.xxxLabel extract tr).canFlow Label.pub tr.erase)
:= by
  simp only [Bytes.XXXHasUsage, Bytes.xxxLabel]
  split <;> grind [Bytes.HasUsage]

/-- Port of `mk_has_xxx_usage_publishable`. -/
public
theorem Bytes.XXXHasUsage_public
  [GetUsage] [GetLabel]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
  : (b.xxxLabel extract tr).canFlow Label.pub tr.erase →
    b.XXXHasUsage extract usg tr
:= by
  simp only [Bytes.XXXHasUsage, Bytes.xxxLabel]
  split <;> grind [Bytes.HasUsage]

/-- Port of `is_secret`. -/
@[expose]
public
def Bytes.IsSecret [BytesInvariants] (l: Label) (b: Bytes) (tr: ProofTrace): Prop :=
  b.Invariant tr ∧
  b.label tr = l

end Predicates

section Later

variable [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor] [BytesInvariants] [BytesInvariantsProofs]

/-- Bytes knowable by a label stay knowable by it when the trace grows (DY* uses SMT patterns, as DyLean's `Bytes.Publishable_later_fast`). -/
public
theorem Bytes.KnowableBy_later (l: Label) (b: Bytes) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    b.KnowableBy l tr1 →
    b.KnowableBy l tr2
:= by
  grind

grind_pattern Bytes.KnowableBy_later => tr1 ≤ tr2, b.KnowableBy l tr1
grind_pattern [grind_later] Bytes.KnowableBy_later => tr1 ≤ tr2, b.KnowableBy l tr1

end Later

end DY
