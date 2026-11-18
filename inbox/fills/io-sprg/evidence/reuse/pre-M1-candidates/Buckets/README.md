# Bucket proof candidates

Read-only preparation for the explicit optional indexMap design in Buckets.lean.
Every `.proof` is one replacement body for the correspondingly named existing
M0 theorem. Candidates are unelaborated: no Lean, Lake, exact?, apply?, build,
cache, seal, or axiom command ran, and no implementation source was edited.
Every tactic candidate was written in a separate tool invocation with one outer
`by` and no nested tactic blocks. The two rank candidates are delegated to the
same read-only workflow; their notes identify the generic public order/card facts.

Suggested dependency order: rank_lt_load, eq_of_rank_eq, indexMap_some/none,
indexMap_injective_on_bucket, bucketMatrix_apply_indexMap. The final support-card
bound is independent of all sorried positional-injectivity helpers and works even
when placement is overfull. It relies only on the matrix and bucket readers.
Do not use the current unresolved theorem constants as search facts or probe
shortcuts. Replace upstream holes and check them before testing their consumers.

## Public reuse for positional/matrix candidates

| Fact | Exact Mathlib location | Use |
| --- | --- | --- |
| `le_of_not_gt`, `LT.lt.trans_le` | Existing ordered-Nat API | Convert non-overfull capacity into rank<rc*rc using the proved rank bound. |
| `Equiv.injective`, inverse equivalence injectivity | Existing Equiv API; actual `finProdFinEquiv` at `Logic/Equiv/Fin/Basic.lean:325` | Equality of optional grid coordinates recovers equality of their explicit finite ranks. No division/modulo proof or new grid enumeration. |
| `Option.some.inj` | Existing constructor injectivity | Remove `some` before inverse-equivalence injectivity. No optional-value decoder or classical choice. |
| `Finset.sum_eq_single` | `Algebra/BigOperators/Group/Finset/Basic.lean:348`, generated additive counterpart of `prod_eq_single` | Isolate the correction at j. Other summands vanish by within-bucket positional injection. |
| `Finset.exists_ne_zero_of_sum_ne_zero` | Same file `:514`, generated additive counterpart of `exists_ne_one_of_prod_ne_one` | A nonzero matrix entry receives a nonzero supported correction; cancellation can only shrink matrix support. Requires only AddCommMonoid. |
| `Finset.card_image_of_injective` | `Data/Finset/Card.lean:238` | Mapping matrix-support positions to `some position` preserves cardinality. |
| `Finset.card_le_card` and `Finset.card_image_le` | `Data/Finset/Card.lean`, image bound at `:214` | Support image is contained in the image of supported outputs under indexMap; this proves the support cardinal bound with no chosen witness map. |
| `Finset.mem_image`, `mem_filter`, `mem_inter` | Existing finite-set APIs | Specialize the matrix-support and source-support membership arguments. |

Only own published readers (`overfull_iff`, `rank_eq`, `load_eq`, `bucket_eq`,
`indexMap_eq`, `bucketMatrix_eq`) are supplied to rewriting. No Mathlib definition
is supplied to simp/rw/unfold. The support bound uses local let abbreviations S/T,
not a new global definition. No product sampler, algorithmic prime finding, or
chosen finite encoding is introduced.

The matrix support proof uses the injective map `c -> some c` on the support and
the possibly noninjective image map `j -> indexMap j` on `bucket intersect bad`.
Thus it avoids constructing an arbitrary preimage selector. A zero-ring case,
empty grid, empty bucket, or cancellation of corrections causes no problem.
The optional `none` coordinates of supported outputs can only add one image point;
they are never used to represent a nonzero matrix position.

## Lead check points

The snippets rely on the existing Fin product's eta equality for `(c.1,c.2)=c`;
if elaboration wants it explicitly, use `Prod.mk.eta` as a theorem, not an unfolding.
For the support-card image proof the explicit `(f := fun c => some c)` parameter
may help inference if the expected image does not determine it. All indexMap proof
bounds are proposition proofs, so proof irrelevance identifies the Fin witnesses.
The file's existing Matrix imports reach the finite-sum API; no new Mathlib root
is proposed. Confirm those implicit/type arguments in the authorized lead checks.
