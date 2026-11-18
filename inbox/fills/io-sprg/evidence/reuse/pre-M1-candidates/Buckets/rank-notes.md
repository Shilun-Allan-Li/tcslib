# Bucket rank proof candidates

Snapshot: HEAD `b80bfb9011f7bf39ec1548467c27dda102e2d0e9`; `Buckets.lean` SHA256
`02849ec3ce375221bf1255d484944fb72a65d3c660cee70f054d3dea6a74a086`. Actual source inspected:
`TCSlib/Cryptography/Obfuscation/StructuredSeed/Buckets.lean`.

Status: two **unelaborated proof candidates**, each intended to replace only the
corresponding theorem's `sorry`. No Lean/Lake/build/cache command was run. No root
source or indexMap/matrix proof was edited. `exact?`/`apply?` remain lead-only pending
checks. These notes and both snippets are staged only under `/private/tmp`.

## Owner definitions and readers

- `bucket` is `univ.filter (fun j => phi j = b)`, reader `bucket_eq` at line 56.
- `load` is the fiber cardinal, reader `load_eq` at line 64.
- `rank` is the cardinal of `univ.filter (fun i => i < j and phi i = phi j)`,
  reader `rank_eq` at line 81.
- Targets inspected: `rank_lt_load` at line 103 and `eq_of_rank_eq` at line 110.
  Their own or downstream sorried theorem bodies were not used as search facts or
  premises of these candidates. The second candidate does not invoke the first.

## Public API search and selected reuse

| Public existing API | Exact source location | Use / assessment |
| --- | --- | --- |
| `Finset.orderIsoOfFin` | `.lake/packages/mathlib/Mathlib/Data/Finset/Sort.lean:181` | Gives `Fin k` order-isomorphic to a finite subset with cardinal `k`. Considered before direct cardinal proof. |
| `Finset.orderIsoOfFin_symm_apply` | same file `:197` | Identifies the inverse with the sorted list's `idxOf`, not directly the current predecessor-filter cardinal. A new bridge to that cardinal would still be needed. |
| `Fin.card_Iio` | `.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Fin.lean:891` | Gives the cardinal of an initial interval in `Fin`; applying it to the fiber subtype likewise requires transport/order-isomorphism and filter-cardinality bridges. |
| `Fintype.card_Iio` | `.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Defs.lean:420` | Converts subtype cardinal to finite interval cardinal, but does not identify the current ambient filtered fiber automatically. |
| `Finset.card_lt_card` | `.lake/packages/mathlib/Mathlib/Data/Finset/Card.lean:296` | Selected: turns an explicit strict subset into strict cardinal inequality. The generic cardinal argument is reused, not rederived. Already available through the owner's direct import. |
| `Finset.ssubset_iff_of_subset` | `.lake/packages/mathlib/Mathlib/Data/Finset/Defs.lean:306` | Selected: strictness is witnessed by the current/earlier index after the explicit filter inclusion. |
| `Finset.filter_ssubset` | `.lake/packages/mathlib/Mathlib/Data/Finset/Filter.lean:129` | Considered. Direct use would first rewrite the two-condition ambient filter as a filter of its fiber. The submitted candidate instead gives the concrete fiber-specific inclusion and witness directly. |
| `Finset.monotone_filter_right` | same file `:191` | Alternative generic inclusion lemma; explicit predicate transport is two term constructors in these candidates, so no additional helper is stated. |
| `Finset.mem_filter`, `Finset.mem_univ` | public Finset membership API | Selected term-level constructors/projections for the fiber-specific subset and witness. |
| `lt_trans`, `lt_irrefl`, `lt_trichotomy`, `ne_of_lt` | public order API | Selected to compare earlier elements, reject self-precedence, and dispatch the final linear-order cases. |

Searches covered name and conclusion shapes under Mathlib's Finset, Fintype, Order,
and interval files, plus TCSlib examples. No direct public theorem for equality of
these exact fiber-predecessor counts or their injectivity was located. No use was
made of downstream StructuredSeed rank/indexMap/cardinality statements. The
order-iso route would add imports (`Sort`/intervals) and a nontrivial identification
lemma while still needing the same membership work. The selected route adds no
Mathlib root and makes only the construction-specific strict-subset step.

TCSlib examples `BooleanAnalysis/Switching/CanonicalDTree.lean:24` and
`Complexity/SpaceComplexity/ExpBFS/Search.lean:72` demonstrate ordinary reuse of
`Finset.card_lt_card`, not a theorem whose conclusion duplicates either target.
Initial broad queries named some absent file paths; the subsequent explicit existing
paths above were read. No successful exact?/apply? or exhaustive search claim is made.

## Candidate 01: rank below load

The prior indices in the same fiber are a subset of that fiber. The fiber contains
`j`, but the prior-index filter cannot contain `j` because `j < j` is false. Apply
`Finset.card_lt_card`. Only owner equation readers are passed to `rw`.

Uncertainty: this is a straightforward source-level candidate, but theorem argument
inference and tactic elaboration have not been tested. No mathematical obstruction
was found. It works vacuously whenever there is a supplied `j : Fin m`, including
all nonempty ambient cases; it requires no positivity hypothesis for `B` separately.

## Candidate 02: equal same-bucket ranks imply equal indices

A local `hstrict` proves strict increase for two ordered indices in the same fiber:
all predecessors of `a` are predecessors of `b`, while `a` itself is a predecessor
of `b` and not itself. This is the construction-specific predicate transport; the
cardinal strictness is again the public `Finset.card_lt_card` theorem. Linear-order
trichotomy on `i,j` then contradicts rank equality in either strict case.

The local fact is not an imported sorried helper, and it does not depend on
`rank_lt_load`. No generic order/cardinality theorem is re-proved. The snippet has
one outer tactic block; the local fact is discharged through a bullet subgoal, not
a nested tactic-block opener.

Uncertainty: the compact tuple patterns and elaboration of
`(Finset.ssubset_iff_of_subset ?_).2 ?_` require the lead's one-slot Lean test.
The explicit membership types determine both finite sets; no choice, classical
finite enumeration, extra import, or downstream result is involved.

## Rule-10 / static observations

Both candidates use `rank_eq`, `load_eq`, and `bucket_eq`, as applicable. No foreign
TCSlib definition or Core/Mathlib definition is passed to `simp`, `rw`, or `unfold`.
All Finset and order uses are public theorem applications. No new definitions,
attributes, instances, axioms, sampler constructions, or root-source edits occur.

- `01-rank_lt_load.proof`: 10 lines, max width 66, `1` tactic-block opener, SHA256 `3d170807fe123a6a9c3a58f092860cc45db0c30557503f8afd3f2e24897e933f`.
- `02-eq_of_rank_eq.proof`: 17 lines, max width 75, `1` tactic-block opener, SHA256 `b463b0d5cb05dc3d15b53df376c2f5022fe3b67e6270af73814f6cc14984e615`.
