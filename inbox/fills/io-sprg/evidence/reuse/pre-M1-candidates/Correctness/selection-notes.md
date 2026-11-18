# firstGood selection proof candidates

Snapshot HEAD: `b80bfb9011f7bf39ec1548467c27dda102e2d0e9`. Sources inspected read-only in
`/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange`.

Status: **unelaborated candidates only**. No Lean, Lake, build, cache, source edit,
new generic List helper, or use of any target's sorried body was performed. The
snippets are replacement proof bodies for `Correctness.lean:56` and `:64`.
No candidate for `firstGood_some_minimal` was attempted.

## Exact existing public APIs

| Existing fact | Source location | Role |
| --- | --- | --- |
| `Params.firstGood_eq` | `TCSlib/Cryptography/Obfuscation/StructuredSeed/Samplers.lean:190` | Owner reader: rewrites the construction's search to `(List.finRange kappa).find? flags`. |
| `List.find?_eq_none` | `/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/Find.lean:227` | Exactly `find? p l = none iff forall x in l, not p x`. |
| `List.find?_some` | same file `:280` | Exactly `find? p l = some a -> p a`, where a Boolean coerces to its equality with `true`. |
| `List.mem_finRange` | `.lake/packages/mathlib/Mathlib/Data/List/FinRange.lean:29` | Every `k : Fin kappa` belongs to the searched finite list, including vacuous `kappa=0`. |
| `Bool.eq_false_iff` | `/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Bool.lean:61` | Exactly `b = false iff b != true`, converting the search theorem's Boolean negation to the requested false flag. |

The none candidate rewrites through the first two readers, then applies membership
and `Bool.eq_false_iff` in the two directions. The reverse direction simply ignores
the membership premise because every flag is already false. The some candidate
rewrites the supplied search equation through the owner reader and applies
`List.find?_some` directly. Both reuse the generic List result instead of proving
it again. No positivity, nonempty-list, or nonzero security-parameter hypothesis
is added.

Name/shape searches also found existing TCSlib uses in
`Complexity/BranchingPrograms/Barrington.lean:418`/`:422` and
`Cryptography/Asymptotic/OneWayLemmas.lean:902`; these corroborate the direct public
API pattern. The code does not use those examples as lemmas or import them.
The original correctness owner notes already name these public source facts.
One initial query named nonexistent `Init/Data/Bool/Basic.lean` and `Lemmas.lean`;
the actual pinned `Init/Data/Bool.lean` was then located and read.

## Rule 10 and remaining uncertainty

Only the construction's named `firstGood_eq` reader is used to read its foreign
TCSlib definition. `rw` receives that reader and the public theorem
`List.find?_eq_none`; no List/Bool definition is passed to rewriting or unfolding.
There is no induction, generic helper, custom sampler, choice, new import, or
additional assumption. Existing imports already include `List.finRange` membership
through the construction's SparseFactor dependency.

The only remaining uncertainty is Lean elaboration of Boolean-to-Prop coercions
and inferred `find?` parameters. The inspected theorem types match exactly, but
no kernel test or exact?/apply? probe has been run; the lead owns those checks.
Each snippet has one outer tactic block and no nested tactic-block opener.

- `01-firstGood_none_iff.proof`: 7 lines; max width 59; 1 tactic-block opener; SHA256 `585e598d2e624d18a13aa6f04a27ddb39fbf5d88dcb9c7176f57843286f1119c`.
- `02-firstGood_some_flag.proof`: 3 lines; max width 25; 1 tactic-block opener; SHA256 `1ad6c76553189b2a2ca38277be3ba1c24933730586340dfecc76815d7f0c399d`.
