# SparseFactor M1 proof candidates — NOT RUN

Prepared 2026-11-18, read-only against the managed io-sprg worktree. No Lean,
lake, build, cache, source edit, or git mutation was performed. Every proof
below is a candidate for the root's one-process Lean slot, not kernel evidence.
The source/mathlib binding is in source-binding.json. The source file was150
lines; all five nonreader statements are unchanged by these replacement bodies.

The candidates use the existing row-major functions exactly as defined. They
add no generic helper, no definition, no assumption, and no import. In
particular, there is no chosen enumeration, no rank argument, no positivity
assumption on rows/cols/t, and no change to deterministic padding.

## Insertion order and dependencies

| Existing theorem | Replacement body | Public reuse | Dependencies |
|---|---|---|---|
| sparseEntries_nodup | 01-sparseEntries_nodup.lean.txt | List.Nodup.product, List.Nodup.filter, List.nodup_finRange | sparseEntries_eq |
| mem_sparseEntries_iff | 02-mem_sparseEntries_iff.lean.txt | List.mem_filter, List.mem_product, List.mem_finRange, decide_eq_true_eq | sparseEntries_eq |
| sparseEntries_length_eq_card | 03-sparseEntries_length_eq_card.lean.txt | List.toFinset_card_of_nodup, List.mem_toFinset, Finset.ext/filter/univ readers | first two theorems |
| sparseFactor_mul | 04-sparseFactor_mul.lean.txt | Matrix.mul_apply, Finset.sum_eq_zero/sum_eq_single, List.mem_iff_getElem, List.getElem?_eq_some_iff, List.getElem?_inj | sparseEntries_nodup, mem_sparseEntries_iff, factor/left/right readers |
| sparseFactor_mul_of_card_le | 05-sparseFactor_mul_of_card_le.term.txt | equality transport | length/card theorem, sparseFactor_mul |

Keep each original theorem's docstring and proof sketch when inserting. The
45-line reconstruction candidate has step comments aligned with that sketch.
All candidate lines are at most100 characters. Each tactic candidate contains
one top-level tactic block; the final card-bound candidate is a term.

## Reconstruction argument

1. Read the factor pair through sparseFactor_fst/snd and expand ordinary matrix
   multiplication with Matrix.mul_apply. Read both matrix functions through
   sparseLeft_eq and sparseRight_eq.
2. If the target entry M i j is zero, inspect each slot. Missing slots multiply
   zero by zero. A present slot contributes only if both selected coordinates
   equal(i,j); in that case its stored entry is also zero. Finset.sum_eq_zero
   then yields the target value.
3. If M i j is nonzero, mem_sparseEntries_iff and List.mem_iff_getElem produce
   an existing slot q below the sparse list's length. The length<=t hypothesis
   embeds that same natural q into Fin t. No default position is needed.
4. Finset.sum_eq_single keeps this slot, whose contribution is M i j*1. For any
   other slot, either getElem? is none, or one selected coordinate differs.
   If both coordinates agree, List.getElem?_inj plus sparseEntries_nodup forces
   the slot index to equal q, contradicting the off-diagonal hypothesis.
5. Translate a cardinality bound into the length bound by the existing length
   equality. There is no second factorization proof.

This proof handles t=0 without a separate convention: a nonzero target would
produce q<t=0, while all-zero matrices have only zero summands. Empty matrix
row/column types are vacuous under matrix extensionality. A zero semiring is
allowed. No commutativity of multiplication or field structure is used.

## Required probes still pending root

The provided probe-exact.lean.txt and probe-apply.lean.txt are reusable body
replacements. For EACH of the five existing theorem statements, root should
run the exact? and apply? body separately, one owner/probe at a time, recording
the actual suggestion or failure. Do not import the completed SparseFactor
module and restate its theorem in a scratch namespace: exact? could then use
the original sorried theorem, which would not be a meaningful reuse search.
Instead replace that theorem's sorry temporarily in its owner source/probe
before the theorem is available to name search, with earlier helpers already
proved or accurately marked as dependencies.

No exact?, apply?, simp?, elaboration, axiom, or seal result is claimed here.
The root should first check the three short enumeration/cardinality proofs,
then the reconstruction. Most likely adjustment points are tactic elaboration
of reader-function rewrites and rw's generated side-goal order; the underlying
argument uses exact published theorem signatures documented in search-log.md.
After real compilation, run the normal source build and canonical coe seals
and update reuse evidence with actual probe output.
