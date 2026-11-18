# PolynomialTensorAlgebra.exists_quadratic_expansion proof draft

Status: complete candidate body by inspection, not natively elaborated. No live source
edits, Lean, lake, build, or Git commands. The candidate has no explicit holes and
introduces no further public helper. All native validation remains with the root.

## Deliverable and header fidelity

`PolynomialExistsQuadraticExpansion.lean.inc` preserves the complete live docstring,
proof sketch, source tag, and searched theorem header. A Python assertion also matched
that header against the root's archived QuadraticExpansionExact anonymous target,
changing only the declaration name. One tactic block, no admitted terms, maximum
line width 90 columns. The by term starts below the existing long final header line,
so the frozen header itself is not reformatted.

## Construction and quantifier order

Use the finite subtype P.support as the monomial index. For each support monomial,
`MvPolynomial.mem_support_iff` supplies the nonzero coefficient premise to hdeg.
The existing proved exists_padded_tuple gives a public length-d tuple and private
length-2 tuple. Classical choice selects both tuples **before** x and y. The private
pair is exactly `(privateTuple s 0, privateTuple s 1)`.

The coefficient witness is:

`C ij tau = sum s : P.support,
  if privatePair s = ij and publicTuple s = tau then P.coeff s.val else 0`.

This is a proof-local finite expression for an existential coefficient family, not a
new public algorithm, representation or efficiency field. No injectivity/uniqueness of
the selected tuples is asserted: all coefficients assigned to the same pair/tuple are
added. The same C is fixed before all variable assignments, exactly as required.

## Evaluation and coefficient collection

1. `MvPolynomial.eval_eq'` and reverse `Finset.sum_coe_sort` expand evaluation as a
   sum over the support subtype, with the full finite variable power product.
2. `Fintype.prod_sum_type` separates the public/private exponent factors; the sum-type
   case readers expose x and y. Reverse hpub/hpriv instantiate the two existing padded
   product identities, and `Fin.prod_univ_two` reads the two private factors. Multiplicative
   associativity aligns the term order. This proves the local hEval identity.
3. Expand only the proof-local C, using `Finset.sum_mul` to move its finite support sum
   through the three scalar factors. A precisely typed `Finset.sum_comm` specialization
   first moves the support sum past the public tuple sum, then ordinary sum_comm moves
   it past the private-pair sum.
4. For one supported monomial, existing ite_and/ite_mul and zero_mul readers expose
   the two selection conditions. `Finset.sum_ite_irrel` moves the pair condition out
   of the tuple sum; `Fintype.sum_ite_eq` selects the assigned public tuple and private
   pair. No generic fibre-sum proof is rederived or published.

The proof needs no division by two, coefficient matrix symmetry, nonzero-ring hypothesis,
prime modulus, dimension positivity or basis independence as polynomial functions.
It works over the exact supplied CommSemiring R, including a zero semiring; empty support,
empty public/private variable sets, and d=0 are handled by the same finite identities.

## Exact reused APIs and source references

- Same live module :53, exists_padded_tuple. Root reports this body native PASS;
  its witness precedes the variable assignment and has exactly the product orientation
  consumed by reverse hpub/hpriv. The proof is inspected, not copied here.
- Mathlib Algebra/MvPolynomial/Basic:543, mem_support_iff.
- Mathlib Algebra/MvPolynomial/Eval:241, eval_eq'.
- Mathlib Algebra/BigOperators/Group/Finset/Basic:449, sum_coe_sort, the published
  additive counterpart of prod_coe_sort.
- Mathlib Data/Fintype/BigOperators:245, prod_sum_type.
- Mathlib Algebra/BigOperators/Fin:107, prod_univ_two.
- Mathlib Algebra/BigOperators/Ring/Finset:49, Finset.sum_mul.
- Mathlib Algebra/BigOperators/Group/Finset/Sigma:117 additive counterpart,
  Finset.sum_comm (same standard finite-sum interchange).
- Mathlib Algebra/BigOperators/Group/Finset/Defs:550 additive counterpart,
  Finset.sum_ite_irrel.
- Mathlib Algebra/BigOperators/Group/Finset/Piecewise:288 additive counterpart,
  Fintype.sum_ite_eq (fixed index equals summed variable).
- Core/Mathlib ite_and, ite_mul, zero_mul, sum_const_zero, mul_assoc and sum case readers.

No foreign TCSlib or Mathlib definition is explicitly passed to simp/rw/unfold. C and
privatePair are proof-local let bindings only. The module remains Mathlib-only and
acyclic with Classes. A potential native elaboration concern is whether `choose` is
already available in the existing imported tactic closure; if a precise extra import
is needed, its home is Mathlib.Tactic.Choose, not a new proof helper. No import is
changed by this delivery.

## Native reuse-search prerequisite

`evidence/search/arbitrary-group-and-expansion/run/results.jsonl` records root searches:
QuadraticExpansionExact rc1 with one expected no-proof error; Apply rc0 but with one
remaining admitted search result and only partial existence-wrapper suggestions.
There was no full match. These probe results justify drafting the searched statement;
they are not a native PASS of this newly supplied proof body.

## Actual searches/reads in this invocation

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
cat TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PolynomialTensorAlgebra.lean
cat evidence/search/arbitrary-group-and-expansion/expansion.statement.txt
sed -n '234,247p' .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean
rg -n -A 7 -B 3 'sum_coe_sort|prod_coe_sort' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/*.lean .lake/packages/mathlib/Mathlib/Data/Fintype/*.lean | head -75
sed -n '240,257p' .lake/packages/mathlib/Mathlib/Data/Fintype/BigOperators.lean
sed -n '284,299p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean
rg -n 'sum_coe_sort|sum_comm.*sum_comm|sum_mul.*ite_and|ite_and.*sum_ite_eq' TCSlib/BooleanAnalysis TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial | head -45
rg -n -A 5 -B 3 'sum_ite_irrel|prod_ite_irrel|ite_sum|ite_prod|sum_ite.*const|sum_ite.*prop' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/*.lean | head -85
rg -n 'sum_comm \(t :=.*support|sum_comm \(s :=.*support|sum_comm.*Subtype|sum_comm.*\(α :=' TCSlib .lake/packages/mathlib/Mathlib | head -30
rg -n 'choose .* using fun .*support|choose .* using fun .*:' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial | head -20
rg -n -A 4 -B 2 'theorem sum_mul|theorem mul_sum|lemma sum_mul|lemma mul_sum' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean | head -35
```

Also read the archived QuadraticExpansionExact source to check the complete header and
its namespace/options context. The nearest sum-coe-sort and irrelevant-condition-sum
lemmas were read at their actual declarations, not reconstructed from their names.

## Verification limits

Static exact-header/doc, line-width, one-block and absence-of-admission checks passed.
Native typechecking, choose tactic availability, typed support-sum interchange,
conditional singleton simplification, and standard-axiom checking remain for root.
No false claim or mathematical obstruction was found; no explicit hole is concealed.
