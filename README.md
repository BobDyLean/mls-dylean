# MLS-DyLean

Port of [MLS\*](https://github.com/Inria-Prosecco/mls-star),
from [F\*](https://github.com/FStarLang/FStar)/[DY\*](https://github.com/REPROSEC/dolev-yao-star-extrinsic)
to [Lean](https://github.com/leanprover/lean4)/[DyLean](https://github.com/BobDyLean/dylean).
See the [porting notes](PORTING_NOTES.md).

**LLM disclosure.**
The specification, tests, and security theorem statements
were *translated* from MLS\* using LLMs,
and were audited line by line to ensure their accuracy
with respect to MLS\*.
The statements of the intermediate lemmas and the overall proof structure
were *translated* from MLS\* using LLMs,
but were not audited
because they are only helpers
to prove the security theorems.
The proofs
were *synthesized* by LLMs,
because the proof mechanisms of F\* and Lean
are different enough
that a direct translation is not possible.
The bindings for OpenSSL were entirely done by LLMs
and went through zero audit, and hence must be treated as slop;
they are fine for running the test vectors,
but must not be used in production
(and anyway,
this executable specification of MLS
has not been externally audited for security).

## How to build

1. [Install Lean](https://lean-lang.org/install/)
2. `lake build` to check the proofs
3. `lake test` to run the tests (requires installing OpenSSL headers)

## What is verified?

We prove security properties for TreeKEM.
The security properties of TreeSync as a standalone protocol are not ported from MLS\*,
but most of the intermediate lemmas are ported, as they are needed to prove the security properties of TreeKEM.
No security properties are proven for TreeDEM (same as MLS\*).

## Related papers

Papers on MLS\*:

- TreeKEM: A Modular Machine-Checked Symbolic Security Analysis of Group Key Agreement in Messaging Layer Security, IEEE S&P 2025 ([doi](https://doi.ieeecomputersociety.org/10.1109/SP61157.2025.00228)) ([eprint](https://eprint.iacr.org/2025/410))
- TreeSync: Authenticated Group Management for Messaging Layer Security, USENIX Security '23 ([usenix](https://www.usenix.org/conference/usenixsecurity23/presentation/wallez)) ([eprint](https://eprint.iacr.org/2022/1732))
