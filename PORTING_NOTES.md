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

### Randomness

The type `randomness l` used to take as parameter a list of lengths (`l`),
and would enforce that
(1) there exactly `l.length` random bytesring,
and (2) the `i`th bytestring has length `l[i]`.
This parameter is now removed,
and the functions that consume randomness can fail.

## Changes in the cryptography interface

The reuse guard in TreeDEM used to rely on `unsafe_split` + `xor`.
Now, there is instead a dedicated `applyReuseGuard` function.

## Clear separation between specification and proofs

With the goal of using Comparator,
we use a clear separation between specifications and proofs.
In MLS*, the `traceful` functions are often proved to preserve the trace invariants in the same file.
Now, the invariant preservation proofs live in a different file.
Also, in MLS*, there are a few instances where a `traceful` function uses definitions from a code proof file:
such as instance is `path_to_tree_list`, defined in the parent-hash guarantees proof file,
but also used in the `traceful` functions,
to actually log these trees.

## Non-trivial decisions took be the LLM

Manual audit of the code revealed non-trivial design changes took by the LLM,
i.e. changes that do not look line-by-line equivalent to the MLS\* code
(other than the design decisions documented above).

### `MLS.TreeSync.pathToTreeList`

This function outputs the list of subtrees
that would be authenticated by the parent hash of the path leaf.
Typically, these are not all the subtrees from the leaf to the root (after having applied the path):
subtrees that sit at *filtered nodes* (because they have empty sibling)
are omitted from this list.

In MLS\*, the function `path_to_tree_list` (via its companion `path_to_tree_list_aux`)
does this by doing jumps,
using the function `find_node_and_path_parent_hash_link`
which finds the next non-filtered subtree.
To ensure termination of `path_to_tree_list_aux`,
the function `find_node_and_path_parent_hash_link` comes with a post-condition
that the output tree height is strictly smaller than the input tree height.

In here, to avoid this non-trivial termination argument that relies on post-conditions,
the function `find_node_and_path_parent_hash_link` is inlined in `path_to_tree_list_aux`.
The behavior of this function is otherwise the same.

### `MLS.TreeKEM.encryptPathSecretsEntropyLengths`

This function computes the amount of entropy needed
to encrypt the path secrets to their corresponding resolution.
To do this computation properly,
there are two things to notice:
1. the path secrets are encrypted separately to the joiners (in `GroupSecrets`),
   hence this function (whose goal is to create the `UpdatePath` / `UpdatePathNode` ciphertexts)
   must not account the entropy required to encrypt to joiners (which are unmerged leaves)
2. because of filtering,
   not every node on the path to the leaf has a path secret,
   hence this function must ensure to not compute entropy for path nodes that don't exist

In MLS\*, this is taken care by `finalize_create_commit_entropy_lengths` (the only caller of `encrypt_path_secrets_entropy_lengths`),
which achieves (1) by un-adding the joiners,
and achieves (2) by supplying a path of booleans that mirrors the path of optional path secrets,
generated from the tree via `generate_forgotten_path_secrets`,
or from a path of optional path secrets via `forget_path_secrets`,
so that entropy is generated only when there exists a corresponding path secret.
The reason for this path of booleans
is that we cannot know whether a node is filtered from the tree after un-adding joiners:
it is possible that a sibling might be empty because it only contains joiners that were un-added,
hence the corresponding node is not filtered despite having an empty sibling.

In here,
the code is simplified to achieve (2) by shortcuting the path of booleans,
and computing whether a node is filtered by checking whether the sibling is empty anyway
—
despite the careful explanation from the previous paragraph on why we should not do this!
The key observation is that when a node is not filtered
and has empty sibling in the tree with joiners un-added,
then MLS\* would compute the sibling resolution of an empty tree, which yields an empty list,
hence it is the same as if the node were filtered.
