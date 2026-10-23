# Porting Notes

This file documents the main, high-level design changes, compared to MLS\*.
It is human-written.
The LLM took the initiative for lower-level design changes
(e.g. using `UInt32` instead of `nat_lbytes 4`),
such minor design change is documented in the code (by the LLM).

## Use less dependent types

A fundamental difference between F\* and Lean,
is that F\*'s type theory is *extensional*,
whereas Lean's type theory is *intentional*.
In MLS\*,
the specification relies a lot on *dependent types*
because of the extensional type system,
and on *refinement types*
to add pre-conditions,
because they are (most of the time) cheaply discharged by the SMT solver.

### Refinement types / pre-conditions

Overall, this port does not use refinement types / pre-conditions when they are not strictly needed.
Instead, when pre-conditions are not met, the functions have a sensible default behavior
(e.g. the unmerged leaves of an empty node is the empty list).

### Dependent types (trees and paths)

Regarding dependent types,
the main dependent type in MLS\*
are the type of *paths* and *trees*.

The type `tree` of complete binary (sub-)trees is indexed by
- its height (`l` for "levels")
- its tree index (`i`), corresponding to the leaf index of its left-most leaf

The type `path` has the same indices, plus
- the leaf index it targets (`li`)

The purpose of type index `l` is to define the structure of the type:
it is the height of the complete binary tree,
and the length of the path.
However, the type indices `i` and `li` play no such structural role.
There are two reasons they are here in MLS\*.
The first reason is that they give the static guarantee that `tree`s and `path`s are used correctly:
for example, two subtrees with different tree index cannot be swapped,
and a path cannot be applied on another leaf than the one with leaf index `li`.
The second reason is that many functions must anyway *compute* the tree index / leaf index
as we traverse the tree
(e.g. the tree hash includes the leaf index in the hash of leaves,
which must then be computed by the definition of `tree_hash`);
and because `l` and `i` are
(1) indices of the `tree` type
and (2) implicit parameters,
their actual computation is not done explicitly
by functions that recurse on the tree:
their computation is done automatically by unification.

In this port, we only keep the index `l` for `tree` and `path`,
which is useful because it enforces the shape of trees and paths.
It also provides a parameter that trivially decrease,
when recursing on trees / paths.
We drop the indices `i` and `li`,
so Lean's type system does not prevent
to mismatch two subtrees at different positions.
However, to keep recursive functions free from computing the leaf / tree index explicitly
(which is tedious and prone to mistakes),
we provide an interface to recurse on trees that perform this computation.
The base type of trees is `BareTree`, indexed by `l`.
It is then bundled with its tree index `i` (or `position` in the code)
in the structure `Tree`.
To recurse on a tree,
we provide two *views* of a tree:
- the left/right view, for functions that recurse on the whole tree
- the child/sibling view with respect to a leaf, for functions that recurse toward a leaf

Under the hood, the child/sibling view is defined in terms of left/right view,
and the left/right view computes the positions `t.left.position = t.position` and `t.right.position = t.position + 2^(l-1)`.
This allows the function that recurse on trees as clean as in MLS\*.
