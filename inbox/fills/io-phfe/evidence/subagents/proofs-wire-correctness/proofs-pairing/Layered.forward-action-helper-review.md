# Forward-action helpers: search-only delivery

No helper proof, live edit, Lean/lake invocation, Git command, or new agent was used.
The proposed bodies and example bodies are intentional scratch search placeholders.
They are not proof candidates and must not be copied into the live source as admissions.

Snapshot read: 493 lines; SHA-256 09b1074dd541ec70c64dbdf3d8dd93e3c022f82b3724474d804bcf80c5899475.
The current file has 10 substantive admissions. Existing public headers and opening
statement prose are unchanged by this delivery.

## Exact statements and insertion points

The full proposed declarations and source-faithful docstrings are in
`Layered.forward-action-helpers.proposed.lean.inc`, inside the existing
`PartialGarbling.Layered` namespace and `Algorithms` section, with the existing
`{p : ℕ+} {l n d : ℕ}` variables.

1. `forward_node`: put immediately after `forward_root` (currently line 239).
2. `matrix_inl`: put immediately after `matrix_eq` (currently lines 224-225).

The independent root-only probe file imports only the current Layered module plus
`Lean.Elab.Tactic.LibrarySearch`. It uses anonymous examples, so it adds no public names.
Probe each example separately with `exact?` and `apply?`, preserving the other example's
placeholder. Capture both the suggested term and any remaining goals. Neither search has
been run. Do not load the proposed named declarations before these searches.

## Reuse and Rule 10

| Helper | Nearest public statements | Why the helper is source-specific |
| --- | --- | --- |
| `forward_node` | Layered `node_eq`:83, `parent_eq`:89, `lastLabel_eq`:96, `forward_eq`:233; Mathlib `Fin.prod_univ_castSucc` in Algebra/BigOperators/Fin:80; `Fin.init_def` in Data/Fin/Tuple/Basic:489 | Applies an existing finite-product theorem to Layered's parent/node encodings. It does not reprove the generic product recurrence. |
| `matrix_inl` | Layered `matrix_eq`:224, `L1_inl`:188, `L0_inl`:207; PartialGarbling/Defs `publicTensor_apply`:75; Classes `xhat_castSucc`:79, `xhat_last`:83; Mathlib `Matrix.mul_apply` in Data/Matrix/Mul:293; `Fintype.sum_prod_type` in Data/Fintype/BigOperators:251-256; `Fintype.sum_ite_eq'` generated at Algebra/BigOperators/Group/Finset/Piecewise:292-295 | Contracts exactly the source incidence row. Product-index sums and singleton cancellation are consumed from Mathlib. |

Name and conclusion-shape searches over TCSlib, Mathlib and core found no existing
`forward_node`, `matrix_inl`, or equivalent Layered/publicTensor recurrence. The raw
commands and complete focused outputs are in `Layered.forward-action-helper-searches.txt`.
This is text-search evidence only; root exact?/apply? probes remain mandatory.

The broad Kronecker shape search did find Mathlib's
`Matrix.kronecker_mulVec_vec_of_commute` in LinearAlgebra/Matrix/Vec:112 and its related
vectorization theorems. These operate on a whole Kronecker matrix and vectorized matrix.
They do not directly state the source row formula. The entrywise publicTensor reader plus
published singleton sums is the shorter route. Do not create a generic publicTensor
contraction theorem unless a later use warrants it and its own probe is run.

For eventual `forward_action`, use `matrix_inl`, `forward_node`, `Matrix.mulVec`'s public
entry theorem or allowed core/Mathlib reduction, and existing singleton-sum APIs. The output
case expands `L1_inr`, `L0_inr`, swaps the node/tuple sums with `Finset.sum_comm`, collapses
the leaf singleton, and uses `leaf_eq`, `forward_eq`, `polyTensorEval_eq`. There is no need
to prove leaf injectivity: for each fixed tuple the summed node singleton has one index.
No rank, positive-size, nonzero or prime hypothesis is needed; p=1 and l/n/d=0 remain valid.

## Later backward proof: important existing tuple laws

Mathlib Data/Fin/Tuple/Basic already supplies:

- `Fin.append_left_snoc`:653-656;
- `Fin.append_right_cons`:658-661;
- `Fin.append_assoc`:332-335.

The first two are the exact append/snoc/cons reassociations with their canonical length
casts. Reuse them; do not reproduce their proof in an `extend` helper. A source-specific
`extend` specialization can be considered later only after a separate statement search.
Finite-function sum splitting is already available through `Fin.consEquiv.sum_comp` and
`Fintype.sum_prod_type`; an existing use is TCSlib/BooleanAnalysis/Hypercontractivity/
Products/Tensorization:80-85. Its local `hsplit` is not a public lemma to copy.

## Growth estimate and a cycle-free fallback

Current live Layered length is 493 lines. These are engineering estimates of *net* added
lines, including docstrings and proof comments, not checked proof sizes:

| Work | Estimated net growth |
| --- | ---: |
| Three count/coordinate admissions | 40-75 |
| Already supplied forward_root/backward_root terms | about 49 |
| Two proposed reusable forward helpers | 55-90 |
| Existing forward_action proof | 35-65 |
| Backward decomposition helpers plus backward_action | 130-210 |
| rec_spec, translation, privacy | 70-110 |
| Total without extra elaboration/cast reserve | 379-599 |

That gives approximately 872-1092 lines, or about 900-1170 after a modest cast/elaboration
reserve. The 1000-line cap is therefore a real planning risk. The two current helpers fit
beside their definitions; they cannot be moved to an independent file that imports
Layered while Layered imports that file.

If later proof text pushes the forecast above about 900 lines, a legal independent home is
`PartialGarbling/PathAlgebra.lean`, importing precise Mathlib finite-tuple/big-operator
modules and no Layered file. Its theorems must be abstract in the label type, coefficient
function and commutative semiring, so the current module can import it without a cycle.
A useful possible statement is the weighted cons decomposition:

```lean
-- Optional later search target only; no declaration or proof supplied now.
-- Variables: {I R : Type*} [Fintype I] [CommSemiring R].
-- k : ℕ, c : (Fin (k + 1) → I) → R, w : I → R.
(∑ tau : Fin (k + 1) → I, c tau * ∏ i, w (tau i)) =
  ∑ a : I, w a * ∑ tau : Fin k → I,
    c (Fin.cons a tau) * ∏ i, w (tau i)
```

This packages `Fin.consEquiv.sum_comp`, `Fintype.sum_prod_type`,
`Fin.prod_univ_succ`, `Fin.cons_zero`, `Fin.cons_succ`, and distributivity. The searches
found these primitives and existing consumers, not an exact public packaged weighted law.
It still requires its own exact?/apply? probes before being added or proved. Do not move
or reprove generic product, append, sum-reindexing or singleton lemmas in that module.
This fallback alone may save only tens of lines; the full backward proof must be measured
before choosing the final split. No mathematical obstruction was identified.
