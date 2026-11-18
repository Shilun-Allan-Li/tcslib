# Direct canonical DLIN column laws: minimal header proposal

DESIGN ONLY. No new proof is supplied or run. The two term `sorry` markers in the header
fragment are admission placeholders for native statement/reuse probes, not proof candidates.
No Lean/lake/build/Git, live edit, process operation, sampler/machine, extra agent, or native
search was run by this child. All main frozen declarations remain unchanged.

## Recommended API and cycle-free home

Two new finite-field bounded-test headers are in ColumnLaws.helper-headers.lean.inc:

1. Pairing.dlin_real_column_gap_le, exact loss 1/N^2.
2. Pairing.dlin_random_column_gap_le, exact loss 1-(1-1/N)^3.

Both quantify a finite Field K, a natural row count (including zero), and an arbitrary
[0,1]-valued test H of a two-column scalar base matrix and one scalar response vector.
No group, generator, security parameter, fixed schedule, response-column dimension, advice,
realiser, machine or full-hybrid security assertion occurs. They therefore do NOT restate
mddhAdv_le. These are generic scalar column laws that its proof can consume at a single
fixed hybrid and fixed other-column masks. This is the smallest useful pair of compound
laws: rank geometry, uniform image, and its exceptional mass are exposed exactly once.

Proposed independent home: TCSlib/Cryptography/Pairing/MatrixDH/ColumnLaws.lean.
Direct imports proposed for the root probes:
  TCSlib.Cryptography.Pairing.MatrixDH.FiniteLinear
  Mathlib.Logic.Equiv.Fin.Basic
FiniteLinear already imports probability/bridge/OneWay, Matrix.NonsingularInverse and its
determinant dependencies. The exact direct-root list is lead-owned, subject to native probe
and official fillinputs/cache checks. No new Mathlib root is claimed already cached.

ColumnLaws must NOT import Linear, MatrixDH.Defs or SelfReduction. SelfReduction may import
ColumnLaws; this yields no cycle (current Defs imports Linear, which imports Diagonal).
No Diagonal import is needed by these two generic laws. The existing dlinMatrix definition
is ZMod-specific and resides in Linear; the headers use a statement-local literal finite-
field A rather than importing that later file or introducing a second public algorithm.
At the ZMod consumer, published dlinMatrix_eq identifies the same literal matrix.

## Exact algebra and probability content

Let A(a,b) have rows (a,0), (0,b), (1,1); for uniform L with `rows` rows and three columns,
write M=L*A. Let r,s be uniform coefficient scalars.

REAL: the sampled response is L*(A*(r,s)) = M*(r,s). The column map A^T : K^3 -> K^2 is
surjective exactly when a!=0 OR b!=0. Both zero make its two rows equal; either nonzero
provides a right inverse using the corresponding two independent columns. Thus the only
exceptional event is a=b=0, whose mass is N^-2. The header compares the full actual sample
order ab,rs,L with an independent uniform base M then rs. It does not assert exact equality
on the bad event, or condition sampling on a rank predicate.

RANDOM: the sampled response is L*c, c=(a*r,b*s,t). The augmented matrix
  C = [[a,0,a*r],[0,b,b*s],[1,1,t]]
has determinant a*b*(t-r-s). On a!=0 AND b!=0 AND t-r-s!=0, C is invertible and L*C is a
uniform `rows`-by-three matrix. Its first two columns M and last column v are independently
uniform. Conditional on r,s, translating t by -(r+s) makes the third nonzero test an
independent uniform nonzero-coordinate test, so the exceptional mass is exactly
  1 - (1-1/N)^3 = 3/N - 3/N^2 + 1/N^3.
The random header uses canonical tuple responses (a*r,b*s,t), not the alternate DLIN matrix
presentation with fully uniform first two response coordinates.

The proposed fixed-field claims remain valid in characteristic two and at rows=0. Field
implies positive cardinality/nontriviality; no separate prime/positive-cardinality assumption
is needed. At a concrete ZMod public order, consumers must import Mathlib.Algebra.Field.ZMod
and provide the actual Fact order.Prime / NeZero order instances; Fact/NeZero alone do not
import the missing prime-field instance (the root's confirmed synthetic-Field diagnosis).

## Reuse the existing matrix-image theorem; do NOT prove a right-multiplication variant

For any fixed rectangular A with A^T.mulVec surjective, instantiate
  expect_sample_matrix_mul_of_mulVec_surjective
with M=A^T, r=2, m=3, c=rows and test `fun V => F V^T`.
Reindex the sampled S by the published Matrix.transposeAddEquiv, then use transpose_mul and
transpose_transpose. This is exactly the desired uniform law for L*A, not a new equal-fiber
counting argument. Matrix.mulVec_mulVec turns L*(A*rs) into (L*A)*rs for the real column.
For the random good event apply the SAME theorem with C^T, r=m=3, c=rows. Use
Matrix.det_fin_three for the determinant expression and
Matrix.mulVec_surjective_iff_isUnit / Matrix.isUnit_iff_isUnit_det plus field isUnit_iff_ne_zero
for square surjectivity. Matrix.mul_assoc is available if formulating right-inverse witnesses;
no repeated generic rank/image proof is needed.

For a sampled uniform `rows`-by-three output U, use the existing equivalence
  (Equiv.arrowCongr (Equiv.refl (Fin rows)) (Fin.succFunEquiv K 2)).trans
    (Equiv.arrowProdEquivProdArrow (Fin rows) (fun _ => Fin 2 -> K) (fun _ => K))
to split U into (first-two-column matrix, last column vector), then expect_sample_equiv and
Bridge.expect_sample_pair. These are published finite-function equivalences, not a new
sampling algorithm. Fin.castSucc/Fin.last identify the coordinates via their public readers.
If the native notation/implicit arguments need adjustment, root should repair the probe
before any helper proof; no equivalence code has been authored or claimed to typecheck here.

## Existing shared probability law already prevents copying Diagonal.hBadMass

The live Diagonal proof has a LOCAL proved hBadMass for a=0 OR b=0 with mass 2/N-1/N^2.
It cannot be cited outside its proof. Copying that calculation would be unnecessary and
would obscure the different real event (AND, not OR).

Static search found a PUBLIC generic theorem that covers BOTH needed counts directly:
  OneWay.uprob_pi_forall (OneWayFunctions/Basic.lean:118).
It states Pr[forall i, p(xs_i)] = Pr[p]^card(i). Together with
  Bridge.prob_sample_eq_uprob (:66),
  OneWay.uprob_eq_one_div_card (:144),
  Foundations.uprob_not (Foundations/Probability.lean:109),
it gives the real AND-zero mass at Fin 2 using p(x):=x=0, and the random triple-nonzero mass
at Fin 3 using p(x):=x!=0 after the t translation. Fin.forall_fin_two and Fintype.card_fin
read the finite-coordinate conditions. Probability.prob_not is an alternative complement
reader if keeping the sample form. expect_sample_equiv / uprob_comp_equiv and
Bridge.expect_sample_pair / Foundations.uprob_prod handle the scalar translations/products.

Therefore the recommended MINIMAL plan is NO new shared counting helper and NO extracted
copy of Diagonal.hBadMass. Root can also refactor that local proof to consume the same
public independent-coordinate theorem when convenient. If a public ProbComp pi-count
wrapper is later desired, it should be an explicitly requested thin bridge/extraction with
its own native reuse probes, NOT a separate hand-written counting argument. No such extra
header/proof is proposed in this minimal pair.

## Fit into the frozen direct reduction and exact slack ledger

For one adjacent MDDH column, fix the other columns' coefficient/uniform masks. Compose H
with the deterministic scalar-to-group exponent encodings and existing D acceptance; this
is a bounded test and introduces no inversion or scalar witness for a group element.
Averaging over L and the other masks is ordinary probability semantics for advice selection,
not new sampling in dlinToMddh (which remains a deterministic function of advice/input/coins).
The two fixed-field losses add to
  1/N^2 + [1-(1-1/N)^3] <= 4/N.
The existing hybrid factor d gives exactly the frozen 4*d/N correction. This ALREADY counts
zero a or b in the canonical tuple route. Do NOT also add dlinMatrixSlack, and do not first
replace the canonical random law by the fully-uniform matrix DLIN presentation. These two
new laws avoid that intermediate presentation altogether.
The remaining mddhAdv_le steps are still separate: actual group-exponent reader identities,
scalar schedule transport, column hybrid, shared averaging selecting one advice family,
and RealizesOn.distinguisherL_eq. The headers neither claim nor hide any of these steps.

## Actual static searches / nearest source references

Read SelfReduction.lean:173-285, the actual mddhPreChallenge/pre/reduction readers, slack and
frozen theorem/proof sketch. Read Diagonal.lean:1-170, including the complete LOCAL hGood/
hBadMass/hPoint proof and its imports. Read current FiniteLinear.lean:40-72 headers/imports.
Read Linear.lean:1-35 and :104-127 for the canonical tuple/matrix distinction and public
ZMod-specific dlinMatrix_eq/dlinMatrix_mulVec. No source PDF was reopened for this design.

Actual name/shape searches in TCSlib Pairing/Games/OneWay and Mathlib matrix/equivalence:
- dlin/column/canonical/rank/augmented/probability shapes; no matching generic pair of
  canonical scalar column laws was found in the inspected scope.
- transpose-multiplication, mulVec/vecMul surjectivity, det_fin_three, determinant units,
  transpose Equiv/AddEquiv/LinearEquiv names; narrowed actual reused definitions/readers.
- fromCols/fromRows and partitioned-matrix readers were inspected as alternatives, but the
  recommended splitting uses Fin.succFunEquiv + arrow-product equivalences instead.
- probability of independent coordinates, scalar singleton/complement/product, sample
  equivalence/commutation and relational sampling. No Games.Closeness import is proposed.

Nearest reused APIs, actually inspected:
- FiniteLinear.expect_sample_matrix_mul_of_mulVec_surjective :49, native proof integration
  pending per parent; no claim it is already standard-only.
- Mathlib/Data/Matrix/Basic.lean:801 Matrix.transposeAddEquiv and public apply reader;
  :830 transposeLinearEquiv (stronger alternative not needed).
- Mathlib/Data/Matrix/Mul.lean:824 mulVec_mulVec, :1032 mulVec_transpose,
  :1036 vecMul_transpose, :1108 transpose_mul; mul_assoc is the existing matrix associativity.
- Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:310/322 surjective iff left/right
  inverse, :118 isUnit_iff_isUnit_det, :336/340 square vecMul/mulVec surjectivity iff IsUnit.
- Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:811 det_fin_three; :800 det_fin_two
  is an optional scalar rank-minor route, not a re-proved determinant formula.
- Mathlib/Logic/Equiv/Fin/Basic.lean:415 Fin.succFunEquiv;
  Mathlib/Logic/Equiv/Defs.lean:450 Equiv.arrowCongr;
  Mathlib/Logic/Equiv/Prod.lean:337 arrowProdEquivProdArrow;
  Equiv.piCongrRight (Basic.lean:147) is an alternative rowwise formulation.
- Games/Probability.lean:304 expect_sample_equiv, :313 expect_sample_comm,
  :409 abs_expect_sub_le_expect; :267 prob_not, :208 prob_eq_expect.
- Games/Bridges/Experiments.lean:66 prob_sample_eq_uprob, :80 expect_sample_pair.
- OneWayFunctions/Basic.lean:118 uprob_pi_forall, :144 uprob_eq_one_div_card.
- Foundations/Probability.lean:109 uprob_not, :153 uprob_prod, :165 uprob_comp_equiv.

Some initial broad rg outputs were truncated; exact narrower source ranges for all APIs
actually recommended were then read. An initial wrong Foundations/Probability path and a
missing variant path were corrected using rg --files; no conclusion relies on the missing
paths. No native exact?/apply? search or header elaboration was run; BOTH headers must be
natively typed/searched by the root BEFORE any proof is attempted. In particular theorem
notation/import roots and the exact finite splitting equivalence remain proposed, not PASS.

## Subsequent status update

Root reports the imported FiniteLinear module now has zero admissions: both the uniform
matrix-image theorem and small-row rank bound passed natively. Both column-law headers
also have VALID root-native typing/exact?/apply? searches at evidence/search/dlin-column-laws/run;
exact? cannot close, apply? offers only partial wrappers, no typing errors. The earlier
pending notes above describe design-time status only. The next real-law skeleton is in
DlinRealColumnGap.skeleton.lean.inc, with one hSurj hole and a separately requested native
helper probe, documented in DlinRealColumnGap-SKELETON.md. No new helper proof exists yet.
