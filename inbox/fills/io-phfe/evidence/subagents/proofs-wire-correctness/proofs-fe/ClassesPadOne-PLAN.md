# pad_one completeness: modular proof plan and reuse inventory

Status: design/search only. No new helper statement or proof has been installed, and no
new helper proof is drafted here. The current invocation's sole tactic block is the
existing phfeClass_eval_eq_quad replacement. All new public helper candidates still
need root-run isolated exact?/apply? probes before proof work. No live changes, Lean,
lake, build, or Git commands.

## Required final statement and edge cases

Keep the existing frozen `Classes.pad_one` header and prose. The supplied bidegree
predicate bounds the public exponent sum by d and the private exponent sum by 2 for
each nonzero coefficient. The required C is an ordered coefficient tensor, evaluated
with both public and private inputs padded by 1. No symmetry condition or division by
2 is involved: a cross coefficient can be assigned to one ordered private pair. This
avoids any characteristic-two or p=1 obstruction. The argument should work over an
arbitrary commutative semiring, specializing to ZMod p only in Classes.

The d=0, l=0, n=0, and p=1 cases are part of the existing claim. Padding coordinates
supply all constant/lower-degree factors; a zero coefficient need not have a tuple
witness. Coefficient selection may use classical choice inside the existence proof;
it must not become a new runtime algorithm or sampler/efficiency contract.

## Cycle-free home

Recommend a new Mathlib-only module
`FunctionalEncryption/PolynomialTensorAlgebra.lean`, namespace
`...FunctionalEncryption.PolynomialTensorAlgebra`. It imports only precise Mathlib
multivariate-polynomial, Finsupp/multiset, finite-tuple and finite-sum roots. It must
not import Classes, FE.Defs.Raw, or another FE construction module.

Classes imports PolynomialTensorAlgebra and applies its generic coefficient-expansion
result as a short adapter. BidegreeAtMost and all existing public names/headers remain
in Classes. The dependency direction is Mathlib -> PolynomialTensorAlgebra -> Classes
-> Layered/Quadratic/PHFE.Data, so there is no parent/child import cycle and no need to
move frozen API declarations merely to add this proof.

Current live Classes measured 615 lines during this invocation. The duplication proof
adds about four net lines. A 20-60-line completeness adapter plus the import keeps
Classes comfortably below 1000. This estimate is planning, not a completed proof count.
Keep the new algebra file below about 800 lines as it develops. If its two independent
stages together grow too large, split them before 1000 into
`PolynomialTensor/Words.lean` and `PolynomialTensor/Expansion.lean`, with Expansion
importing Words and neither importing Classes; use a proper parent facade. No split
or new file is made by this delivery.

## Mathematical decomposition

### Stage 1: bounded exponents become padded tuples

For a finite family of natural exponents with total at most k, represent their
multiplicities as a multiset, choose a list/finite tuple realizing it, and fill the
remaining slots with the distinguished constant label. The witness is fixed before
all assignments of scalar values. Its weight product must equal the original power
product for every assignment into a commutative monoid.

Use existing Finsupp/multiset cardinality and product APIs, List.ofFn reconstruction,
and finite append/constant-product lemmas. Do not write a custom finite enumeration,
multiset count/product theorem, or power-to-repeated-product induction if a published
one applies. A new source-specific padded-word specialization may be required, but
its exact full shape and generic weighted-product variants must be probed first.

Apply this stage twice to each nonzero monomial: k=d on public exponents, k=2 on
private exponents. Padding is the last Fin coordinate so the later Classes adapter
uses the existing xhat_eq and Fin.snoc readers exactly.

### Stage 2: finite support and coefficient collection

Use the existing MvPolynomial.eval_eq' directly rather than re-proving polynomial
expansion. Reindex its finite variable product over the sum type using the published
Fintype.prod_sum_type. The supplied bidegree inequalities give the two Stage 1 bounds.

Choose one public tuple and one private length-two tuple for each support monomial.
Collect coefficients in each tuple-pair fibre with published Finset/Fintype
sum_fiberwise or, if shorter, existing sum_comm and singleton-sum equations.
No injectivity or canonicality of the chosen tuple representation is needed: the
coefficient of a tuple pair is the sum of the original coefficients assigned to it.
The tuple basis need not be independent as functions over a finite residue ring.

The generic result should expose exactly a coefficient family indexed by an ordered
private pair and a public padded tuple, together with the explicit finite evaluation
formula. Keep private degree 2 in the final expansion API; a general tail degree is
not needed for this class claim. A generic bounded-tuple product lemma can still be
used for both the public and private branches.

### Stage 3: existing Classes.pad_one adapter

Transport the private tuple of length two using published finTwoArrowEquiv, and
transport its ordered pair to the existing row-major Fin ((n+1)*(n+1)) coordinate
using finProdFinEquiv. Define the existential PolyTensor witness by that coefficient
family (inside the proof, without a new public algorithm definition).

Read phfeEval_sum, polyTensorEval_eq, and xhat_eq. Existing finite-sum linearity
(Finset.sum_mul, Finset.mul_sum), sum/product equivalence readers and the generic
expansion formula align the expressions. Preserve the original FnClass bit widths
and all encoding interfaces; this proof concerns typed polynomial completeness only.

## Reuse inventory actually found

| Published API | Precise source | Intended use |
| --- | --- | --- |
| MvPolynomial.eval_eq' | Algebra/MvPolynomial/Eval:241 | Evaluation as finite coefficient sum with full finite variable product |
| MvPolynomial.eval_monomial | same:245 | Alternative monomial-level route, if needed |
| MvPolynomial.as_sum | Algebra/MvPolynomial/Basic:946 | Existing polynomial expansion; avoid re-proving it |
| MvPolynomial.support_sum_monomial_coeff | same:942 | Reverse orientation of as_sum |
| Finsupp.toMultiset, card_toMultiset | Data/Finsupp/Multiset:32,62 | Repeated variables and total exponent count |
| Finsupp.prod_toMultiset | same:76 | Existing multiset product/power-product conversion |
| Finsupp.toMultiset_map | same:65 | Map variable labels to values; check the appropriate mapDomain product reader next |
| Finsupp.prod_pow | Algebra/BigOperators/Finsupp/Basic:120 | Finsupp power product equals full finite product |
| Multiset.coe_toList, length_toList | Data/Multiset/Basic:33,59 | Read a multiset through an existing list enumeration |
| List.ofFn_get, exists_iff_exists_tuple | Data/List/OfFn:89,178 | Existing list-to-finite-tuple representation |
| Fin.append_left/right | Data/Fin/Tuple/Basic:291,302 | Fill unused tuple slots with the constant label |
| finTwoArrowEquiv | Logic/Equiv/Fin/Basic:48 | Published length-two tuple/product equivalence |
| Fin.prod_univ_two | Algebra/BigOperators/Fin | Read the two private factors; exact declaration is to be located before use |
| Finset.sum_fiberwise, sum_fiberwise_of_maps_to | Group/Finset/Basic:274,256 additive counterparts | Existing coefficient collection by tuple-pair fibres |
| Fintype.sum_prod_type / prod_sum_type | Data/Fintype/BigOperators:253 / 245 | Nested tuple sums and public/private variable products |

These are public facts, not new proof helpers. Their final precise specializations,
necessary imports, and exact?/apply? outputs must be recorded during the next stage.
No theorem should be postulated on the strength of this planning inventory alone.

## Actual source searches in this invocation

In `/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`:

```sh
rg -n 'pad_one|BidegreeAtMost|homogeneous.*tensor|monomial.*tensor|totalDegree.*degreeOf|eval.*monomial.*prod|exists.*(fin|tuple).*degree' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial .lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct | head -75
rg -n 'theorem.*(sum_monomials_eq|sum_monomial_eq|eval_monomial|degrees|totalDegree)|lemma.*(sum_monomials_eq|sum_monomial_eq|eval_monomial|degrees|totalDegree)' .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Degrees.lean | head -70
rg -n 'toMultiset|prod_pow|sum.*toMultiset|card_toMultiset|prod.*toMultiset|toMultiset.*prod' .lake/packages/mathlib/Mathlib/Data/Finsupp .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial | head -85
rg -n 'exists.*(tuple|fin|list)|exists.*card|ofFn.*Multiset|multiset.*ofFn|Multiset.*ofFn|prod.*replicate|prod_map.*replicate' .lake/packages/mathlib/Mathlib/Data/Multiset .lake/packages/mathlib/Mathlib/Data/Fin/Tuple .lake/packages/mathlib/Mathlib/Data/List/OfFn.lean | head -75
rg -n 'sum_monomials_eq|as_sum|sum.*monomial.*coeff|eval.*sum|eval₂.*sum' .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean | head -60
rg -n 'sum_fiberwise|sum_fiber|sum_ite.*fiber|sum.*fiberwise' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset .lake/packages/mathlib/Mathlib/Data/Fintype .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp | head -50
rg -n 'finTwoArrowEquiv|finTwoArrow|finTwo.*Equiv|piFinTwo|piFin2|Equiv.*Fin 2' .lake/packages/mathlib/Mathlib/Data/Fin .lake/packages/mathlib/Mathlib/Logic/Equiv | head -35
```

Read Eval:234-250, Basic:940-950, Finsupp/Multiset:57-83, List/OfFn:173-184,
current Classes source and import headers, plus the tuple/sum equivalence readers.
An exploratory project search included nonexistent TCSlib/Algebra; the actual generic
algebra facts were located in Mathlib. No generic helper proof has been written.

## Next actionable root steps

1. Integrate/native-check the existing class embedding fragment separately.
2. Choose and freeze one bounded-padded-word helper shape in the Mathlib-only module.
3. Run isolated exact?/apply? against a prefix without that new helper or later admitted
   completeness results. If a complete existing theorem matches, consume it instead.
4. Only then commission its one-block proof, followed by the generic finite coefficient
   expansion and finally the frozen Classes.pad_one adapter.

There is no mathematical obstruction found. The uncertain cost is proof engineering for
multiplicity-to-padded-tuple conversion and finite coefficient collection, not the
existence claim or any modulus restriction.
