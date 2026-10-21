/-!
Port of `MLS.Tree`.

Port-specific differences:
- `tree_index l` is the subtype `{n // 2^l ∣ n}` (`TreeIndex l`). Thanks to proof irrelevance,
  two indices are equal as soon as their values are equal, and the left index of `TreeIndex.zero (l+1)`
  is definitionally `TreeIndex.zero l`.
- The refinements `l == 0` and `l > 0` of the constructors are expressed by their indices:
  `leaf` builds a tree of height `0`, and `node` a tree of height `l+1`.
- `get_child_sibling` returns its result in two cases, instead of a pair whose type depends on `is_left_leaf li`:
  in Lean (intensional type theory) the latter would require casts.
- `path`'s `PNode` is split into `nodeLeft` and `nodeRight`, for the same reason (see `Path`).
- `leaf_index l i` is the subtype `{li // leafIndexInside l i li}`.
-/

namespace Mls

/-! ## Tree indices -/

def TreeIndex (l: Nat) := {n: Nat // 2^l ∣ n}

instance (l: Nat): DecidableEq (TreeIndex l) := fun a b =>
  if h: a.val = b.val then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

def TreeIndex.zero (l: Nat): TreeIndex l := ⟨0, Nat.dvd_zero _⟩

def TreeIndex.left {l: Nat} (i: TreeIndex (l+1)): TreeIndex l :=
  ⟨i.val, Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ l)) i.property⟩

def TreeIndex.right {l: Nat} (i: TreeIndex (l+1)): TreeIndex l :=
  ⟨i.val + 2^l, Nat.dvd_add (Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ l)) i.property) (Nat.dvd_refl _)⟩

/-! ## Trees -/

/--
Type for complete binary tree, with height `l`.
The index `i` represents the leaf index of the leftmost leaf in the subtree.
It does not change the shape of the tree, it is however very useful:
many recursive functions must compute it through the recursive calls,
putting it in the type allows to compute it for free.
It therefore enforces a correct-by-construction tracking of leaf indices,
rules out programmer errors,
and enforces the MLS invariant that two sub-trees at different positions,
even if otherwise identical, are never interchangeable.
-/
inductive Tree (Leaf Node: Type): (l: Nat) → TreeIndex l → Type where
  | leaf {i: TreeIndex 0} (data: Leaf): Tree Leaf Node 0 i
  | node {l: Nat} {i: TreeIndex (l+1)} (data: Node) (left: Tree Leaf Node l i.left) (right: Tree Leaf Node l i.right):
    Tree Leaf Node (l+1) i

def leafIndexInside (l: Nat) (i: TreeIndex l) (li: Nat): Bool :=
  i.val ≤ li && li < i.val + 2^l

theorem leafIndexInside_iff (l: Nat) (i: TreeIndex l) (li: Nat):
  leafIndexInside l i li = true ↔ i.val ≤ li ∧ li < i.val + 2^l
:= by
  simp [leafIndexInside]

def LeafIndex (l: Nat) (i: TreeIndex l) := {li: Nat // leafIndexInside l i li}

def isLeftLeaf {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i): Bool :=
  li.val < i.val + 2^l

/-- The index of the child of `i` containing the leaf `li`. -/
def childIndex {l: Nat} (i: TreeIndex (l+1)) (li: LeafIndex (l+1) i): TreeIndex l :=
  if isLeftLeaf li then i.left else i.right

theorem childIndex_val {l: Nat} (i: TreeIndex (l+1)) (li: LeafIndex (l+1) i):
  (childIndex i li).val = if li.val < i.val + 2^l then i.val else i.val + 2^l
:= by
  unfold childIndex isLeftLeaf
  by_cases h: li.val < i.val + 2^l <;> simp [h, TreeIndex.left, TreeIndex.right]

theorem leafIndexInside_child {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i):
  leafIndexInside l (childIndex i li) li.val
:= by
  have h := li.property
  simp only [leafIndexInside, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1 := of_decide_eq_true h1
  have h2 := of_decide_eq_true h2
  have h3: 2^(l+1) = 2^l * 2 := Nat.pow_succ 2 l
  simp only [leafIndexInside, childIndex_val, Bool.and_eq_true, decide_eq_true_eq]
  split <;> omega

/-- `li` as a leaf index of the child of `i` that contains it. -/
def LeafIndex.child {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i): LeafIndex l (childIndex i li) :=
  ⟨li.val, leafIndexInside_child li⟩

/-! ## Leaf indices of children -/

theorem leafIndexInside_left {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i) (h: isLeftLeaf li = true):
  leafIndexInside l i.left li.val
:= by
  have := leafIndexInside_child li
  simp_all [childIndex]

theorem leafIndexInside_right {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i) (h: isLeftLeaf li = false):
  leafIndexInside l i.right li.val
:= by
  have := leafIndexInside_child li
  simp_all [childIndex]

/-- `li` as a leaf index of the left child, when it is on the left. -/
def LeafIndex.childOfLeft {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i) (h: isLeftLeaf li = true):
  LeafIndex l i.left
:=
  ⟨li.val, leafIndexInside_left li h⟩

/-- `li` as a leaf index of the right child, when it is on the right. -/
def LeafIndex.childOfRight {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex (l+1) i) (h: isLeftLeaf li = false):
  LeafIndex l i.right
:=
  ⟨li.val, leafIndexInside_right li h⟩

/-- A leaf index of the left child, as a leaf index of the parent. -/
def LeafIndex.ofLeft {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex l i.left): LeafIndex (l+1) i :=
  ⟨li.val, by
    have h := (leafIndexInside_iff _ _ _).mp li.property
    have: 2^(l+1) = 2^l * 2 := Nat.pow_succ 2 l
    simp only [TreeIndex.left] at h
    exact (leafIndexInside_iff _ _ _).mpr (by omega)⟩

/-- A leaf index of the right child, as a leaf index of the parent. -/
def LeafIndex.ofRight {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex l i.right): LeafIndex (l+1) i :=
  ⟨li.val, by
    have h := (leafIndexInside_iff _ _ _).mp li.property
    have: 2^(l+1) = 2^l * 2 := Nat.pow_succ 2 l
    simp only [TreeIndex.right] at h
    exact (leafIndexInside_iff _ _ _).mpr (by omega)⟩

theorem isLeftLeaf_ofLeft {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex l i.left): isLeftLeaf li.ofLeft = true := by
  have h := (leafIndexInside_iff _ _ _).mp li.property
  simp only [TreeIndex.left] at h
  exact decide_eq_true (by simp only [LeafIndex.ofLeft]; omega)

theorem isLeftLeaf_ofRight {l: Nat} {i: TreeIndex (l+1)} (li: LeafIndex l i.right): isLeftLeaf li.ofRight = false := by
  have h := (leafIndexInside_iff _ _ _).mp li.property
  simp only [TreeIndex.right] at h
  exact decide_eq_false (by simp only [LeafIndex.ofRight]; omega)

/-! ## Subtrees inside a tree -/

/-- If `a` and `b` are multiples of `n`, and `a < b`, then `a + n ≤ b`. -/
theorem add_le_of_dvd_of_lt {a b n: Nat} (ha: n ∣ a) (hb: n ∣ b) (h: a < b): a + n ≤ b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have: x < y := Nat.lt_of_mul_lt_mul_left h
  have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt this)
  rw [Nat.mul_succ] at this
  exact this

/--
If the subtree at `id` (of height `ld+1`) starts inside the tree at `ip` (of height `lp > ld`),
then so does its left child.
-/
theorem leafIndexInside_left_of_inside {ld lp: Nat} {id: TreeIndex (ld+1)} {ip: TreeIndex lp}
  (h: leafIndexInside lp ip id.val): leafIndexInside lp ip id.left.val
:= by
  simpa [TreeIndex.left] using h

/--
If the subtree at `id` (of height `ld+1`) starts inside the tree at `ip` (of height `lp > ld`),
then so does its right child. This relies on the alignment of tree indices (`TreeIndex`).
-/
theorem leafIndexInside_right_of_inside {ld lp: Nat} {id: TreeIndex (ld+1)} {ip: TreeIndex lp}
  (hl: ld + 1 ≤ lp) (h: leafIndexInside lp ip id.val): leafIndexInside lp ip id.right.val
:= by
  have h := (leafIndexInside_iff _ _ _).mp h
  apply (leafIndexInside_iff _ _ _).mpr
  simp only [TreeIndex.right]
  have hpow: 2^(ld+1) ∣ 2^lp := Nat.pow_dvd_pow 2 hl
  have hip: 2^(ld+1) ∣ ip.val + 2^lp := Nat.dvd_add (Nat.dvd_trans hpow ip.property) hpow
  have := add_le_of_dvd_of_lt id.property hip h.2
  have: 2^(ld+1) = 2^ld * 2 := Nat.pow_succ 2 ld
  omega

/-! ## Paths -/

/--
Type for path in a tree of height `l`, with left-most leaf index `i`,
from the root down to leaf index `li`.
`i` and `li` have no impact on the structure of the type;
however like in `Tree` they prove to be very useful.

MLS*'s `PNode` is split into `nodeLeft` and `nodeRight`, carrying the side of `li`.
In MLS*, the next element of the path is indexed by
`if is_left_leaf li then left_index i else right_index i`, which F* identifies with `left_index i`
when `is_left_leaf li` holds. In Lean, this would require casts,
and the leaf index (whose type depends on the tree index) prevents rewriting.
Use `Path.node` to build a node as `PNode` does.
-/
inductive Path (Leaf Node: Type): (l: Nat) → (i: TreeIndex l) → LeafIndex l i → Type where
  | leaf {i: TreeIndex 0} {li: LeafIndex 0 i} (data: Leaf): Path Leaf Node 0 i li
  | nodeLeft {l: Nat} {i: TreeIndex (l+1)} {li: LeafIndex (l+1) i} (h: isLeftLeaf li = true)
    (data: Node) (next: Path Leaf Node l i.left (li.childOfLeft h)): Path Leaf Node (l+1) i li
  | nodeRight {l: Nat} {i: TreeIndex (l+1)} {li: LeafIndex (l+1) i} (h: isLeftLeaf li = false)
    (data: Node) (next: Path Leaf Node l i.right (li.childOfRight h)): Path Leaf Node (l+1) i li

/-- Port of `PNode data next`: the side is chosen from `li`. -/
def Path.node {Leaf Node: Type} {l: Nat} {i: TreeIndex (l+1)} {li: LeafIndex (l+1) i} (data: Node)
  (nextLeft: (h: isLeftLeaf li = true) → Path Leaf Node l i.left (li.childOfLeft h))
  (nextRight: (h: isLeftLeaf li = false) → Path Leaf Node l i.right (li.childOfRight h))
  : Path Leaf Node (l+1) i li
:=
  if h: isLeftLeaf li then .nodeLeft h data (nextLeft h)
  else .nodeRight (by simpa using h) data (nextRight (by simpa using h))

namespace Tree

variable {Leaf Node: Type}

/--
When dealing with a subtree and a specific leaf in this subtree,
MLS use the term `child` for the child of the subtree containing the leaf,
and the term `sibling` for the other child (that doesn't contain the leaf).
Port of `get_child_sibling`: the child and the sibling are given to the continuation,
together with the proof of the side on which the leaf is.
-/
def getChildSibling {α: Type} {l: Nat} {i: TreeIndex (l+1)}
  (t: Tree Leaf Node (l+1) i) (li: LeafIndex (l+1) i)
  (onLeft: isLeftLeaf li = true → Tree Leaf Node l i.left → Tree Leaf Node l i.right → α)
  (onRight: isLeftLeaf li = false → Tree Leaf Node l i.right → Tree Leaf Node l i.left → α)
  : α
:=
  match t with
  | .node _ left right =>
    if h: isLeftLeaf li then onLeft h left right else onRight (by simpa using h) right left

/-- A tree together with its (hidden) tree index. -/
abbrev SomeTree (Leaf Node: Type) (l: Nat) := (i: TreeIndex l) × Tree Leaf Node l i

/--
`get_child_sibling` returning a pair, where the indices of the child and the sibling are hidden.
Useful when the static link between these indices and `li` is not needed.
-/
def getChildSiblingPair {l: Nat} {i: TreeIndex (l+1)} (t: Tree Leaf Node (l+1) i) (li: LeafIndex (l+1) i):
  SomeTree Leaf Node l × SomeTree Leaf Node l
:=
  t.getChildSibling li (fun _ c s => (⟨_, c⟩, ⟨_, s⟩)) (fun _ c s => (⟨_, c⟩, ⟨_, s⟩))

def getLeafList: {l: Nat} → {i: TreeIndex l} → Tree Leaf Node l i → List Leaf
  | _, _, .leaf data => [data]
  | _, _, .node _ left right => getLeafList left ++ getLeafList right

theorem getLeafList_length: ∀ {l: Nat} {i: TreeIndex l} (t: Tree Leaf Node l i), (getLeafList t).length = 2^l
  | _, _, .leaf _ => rfl
  | l+1, _, .node _ left right => by
    simp only [getLeafList, List.length_append, getLeafList_length left, getLeafList_length right, Nat.pow_succ]
    omega

def leafAt: {l: Nat} → {i: TreeIndex l} → Tree Leaf Node l i → (li: LeafIndex l i) → Leaf
  | _, _, .leaf content, _ => content
  | _, _, .node _ left right, li =>
    if h: isLeftLeaf li then
      leafAt left (li.childOfLeft h)
    else
      leafAt right (li.childOfRight (by simpa using h))

theorem leafAt_ofLeft {l: Nat} {i: TreeIndex (l+1)} (d: Node) (left: Tree Leaf Node l i.left) (right: Tree Leaf Node l i.right)
  (li: LeafIndex l i.left):
  leafAt (.node d left right) li.ofLeft = leafAt left li
:= by
  simp [leafAt, isLeftLeaf_ofLeft]
  rfl

theorem leafAt_ofRight {l: Nat} {i: TreeIndex (l+1)} (d: Node) (left: Tree Leaf Node l i.left) (right: Tree Leaf Node l i.right)
  (li: LeafIndex l i.right):
  leafAt (.node d left right) li.ofRight = leafAt right li
:= by
  simp [leafAt, isLeftLeaf_ofRight]
  rfl

def toString (printLeaf: Leaf → String) (printNode: Node → String): {l: Nat} → {i: TreeIndex l} → Tree Leaf Node l i → String
  | _, _, .leaf data => printLeaf data
  | _, _, .node data left right =>
    "(" ++ toString printLeaf printNode left ++ ") " ++ printNode data ++ " (" ++ toString printLeaf printNode right ++ ")"

def map {Leaf' Node': Type} (fLeaf: Leaf → Leaf') (fNode: Node → Node'):
  {l: Nat} → {i: TreeIndex l} → Tree Leaf Node l i → Tree Leaf' Node' l i
  | _, _, .leaf x => .leaf (fLeaf x)
  | _, _, .node data left right => .node (fNode data) (map fLeaf fNode left) (map fLeaf fNode right)

end Tree

namespace Path

variable {Leaf Node: Type}

def getPathLeaf: {l: Nat} → {i: TreeIndex l} → {li: LeafIndex l i} → Path Leaf Node l i li → Leaf
  | _, _, _, .leaf lp => lp
  | _, _, _, .nodeLeft _ _ next => getPathLeaf next
  | _, _, _, .nodeRight _ _ next => getPathLeaf next

def setPathLeaf {Leaf': Type}: {l: Nat} → {i: TreeIndex l} → {li: LeafIndex l i} →
  Path Leaf Node l i li → Leaf' → Path Leaf' Node l i li
  | _, _, _, .leaf _, lp => .leaf lp
  | _, _, _, .nodeLeft h content next, lp => .nodeLeft h content (setPathLeaf next lp)
  | _, _, _, .nodeRight h content next, lp => .nodeRight h content (setPathLeaf next lp)

end Path

end Mls
