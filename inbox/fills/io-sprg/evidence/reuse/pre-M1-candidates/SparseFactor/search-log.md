# SparseFactor reuse search log — textual evidence only

Worktree: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange.
Mathlib searched IN THIS worktree: .lake/packages/mathlib, git HEAD
029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e. This is the job's current pinned
package source; no external build or copied olean was used. Lean core source
read at /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean.
Source owner SHA and observed fill head appear in source-binding.json.

## Searches made before preparing each proof

1. All TCSlib: `rg -n 'sparse.*(factor|matrix)|factor.*sparse|sparseEntries|Nodup.product|sum_of_injective|sum_eq_single.*get|sum_get' TCSlib --glob '*.lean'`.
   No public sparse factor reconstruction beyond this new owner was found.
   Existing Samplers/Correctness are callers, not reusable proofs. Unrelated
   List index/card applications in TCSlib were inspected by text only.
2. Whole Mathlib: `rg -n 'sparseFactor|sparseEntries|sparse_factor|sparse.*factor|factor.*sparse' .lake/packages/mathlib/Mathlib --glob '*.lean'`.
   No matches. Matrix directory shape searches also found no existing generic
   theorem reconstructing these deterministic list-slot factors.
3. Before nodup: searched List/FinRange/Nodup/Core List for nodup_finRange,
   Nodup.product, nodup_product, and Nodup.filter. Reuse is direct, not a
   reproof of duplicate-freeness for products or filters.
4. Before membership: searched List/ProdSigma/Core List for mem_product,
   mem_filter, and mem_finRange. Reuse is direct Boolean/filter simplification.
5. Before cardinality: searched List/Finset for toFinset_card_of_nodup,
   card_toFinset, mem_toFinset. Reuse existing cardinal theorem then extensional
   membership; do not redo a list-length or cardinal induction.
6. Before reconstruction/padding: searched Core List/Mathlib List for
   getElem?_eq_some, getElem?_eq_none, mem_iff_getElem, getElem?_inj,
   Nodup.getElem_inj_iff, idxOf_getElem. Searched BigOperators for sum_eq_single,
   sum_eq_zero, sum_get/sum_getD/sum_getElem? and Matrix for mul_apply.
   The single-summand proof avoids an unnecessary new generic sum-of-padding
   lemma or a custom bijection between a Fin index and a support subtype.
7. Before cardinal wrapper: existing sparseEntries_length_eq_card and
   sparseFactor_mul exactly compose; no independent mathematical helper.

Two overly broad discovery queries included nonexistent TCSlib/Math and
Mathlib/Data/List/ToFinset.lean paths. Both were corrected by full TCSlib and
Mathlib rg searches; the relevant list membership theorem is actually in
Mathlib/Data/Finset/Dedup.lean. These missing paths are not evidence of absence.

## Exact APIs read from pinned source

| Public API | Source location | Shape used |
|---|---|---|
| List.nodup_finRange | Mathlib/Data/List/FinRange.lean:36 | (finRange n).Nodup |
| List.mem_finRange | Mathlib/Data/List/FinRange.lean:29 | a in finRange n |
| List.Nodup.product | Mathlib/Data/List/Nodup.lean:284 | d1 -> d2 -> (l1 product l2).Nodup |
| List.Nodup.filter | Mathlib/Data/List/Nodup.lean:227 | filter Bool predicate preserves Nodup |
| List.mem_product | Mathlib/Data/List/ProdSigma.lean:39 | (a,b) in product iff both memberships |
| List.mem_filter | Lean Init/Data/List/Lemmas.lean:1272 | membership and Bool predicate=true |
| List.toFinset_card_of_nodup | Mathlib/Data/Finset/Card.lean:201 | card(toFinset l)=length l |
| List.mem_toFinset | Mathlib/Data/Finset/Dedup.lean:116 | finset membership iff list membership |
| Finset.ext | Mathlib/Data/Finset/Defs.lean:151 | pointwise iff -> finset equality |
| Finset.mem_filter | Mathlib/Data/Finset/Filter.lean:123 | finite-set filter membership |
| List.mem_iff_getElem | Lean Init/Data/List/Lemmas.lean:465 | membership -> exists q<hlen, l[q]=x |
| List.getElem?_eq_some_iff | Lean Init/Data/List/Lemmas.lean:221 | l[q]?=some x iff exists bound with l[q]=x |
| List.getElem?_inj | Lean Init/Data/List/Pairwise.lean:302 | q<length -> Nodup -> l[q]?=l[k]? -> q=k |
| Matrix.mul_apply | Mathlib/Data/Matrix/Mul.lean:293 | entry of matrix product is finite sum |
| Finset.sum_eq_single | generated additively from prod_eq_single at Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:348 | off-diagonal zero plus absent-index case |
| Finset.sum_eq_single_of_mem | generated additively from prod_eq_single_of_mem at same file:337 | available alternative if rw side goals are awkward |

Batteries/Data/List/Basic.lean:489 defines List.product as precisely flatMap
of mapped pairs, so the row-major expression is definitionally that product.
The candidate uses change to expose the product membership theorem; it does
not pass a Core/Mathlib definition to simp/rw/unfold. All simplifier arguments
are public lemmas or local equalities/lets. The final factor proof uses own-file
readers and the ordinary Matrix.mul_apply lemma.

A static transitive import walk from the owner's three existing imports found
Mathlib.Data.List.ProdSigma, Mathlib.Data.List.Nodup, and
Mathlib.Algebra.BigOperators.Group.Finset.Basic already reachable (1224 Mathlib
module names visited). No new import/root/cache request is proposed.

## Probe status

| Existing theorem | name/shape rg search | exact? | apply? | candidate Lean check |
|---|---|---|---|---|
| sparseEntries_nodup | done | PENDING ROOT | PENDING ROOT | NOT_RUN |
| mem_sparseEntries_iff | done | PENDING ROOT | PENDING ROOT | NOT_RUN |
| sparseEntries_length_eq_card | done | PENDING ROOT | PENDING ROOT | NOT_RUN |
| sparseFactor_mul | done | PENDING ROOT | PENDING ROOT | NOT_RUN |
| sparseFactor_mul_of_card_le | done; exact same-file composition | PENDING ROOT | PENDING ROOT | NOT_RUN |

These proof bodies complete existing M0 helper statements; no newly invented
helper statement is proposed. Searches do not claim kernel proof or the result
of tactics that this subagent was not permitted to run.
