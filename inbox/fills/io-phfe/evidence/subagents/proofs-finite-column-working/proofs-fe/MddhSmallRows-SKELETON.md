# M1 earliest substantial MDDH dependency: small-row statistical bound

Status: SCRATCH SKELETON, not a complete proof. One tactic block with TWO EXPLICIT TERM
SORRIES: hUniform and hFailure. Exact frozen mddhAdv_smallRows_le header/prose preserved.
All surrounding range/entry/averaging/reader assembly is drafted without further admissions
but has NOT been natively checked. No Lean/lake/build/Git/live edit/extra agent was run.
All proposed helper targets are SEARCH-ONLY and have no supplied proof/native verification.

## Choice after inspecting both files

Read MatrixDH/Defs.lean and SelfReduction.lean remaining original admissions. Before the
self-reduction's full hybrid theorem, Defs.mddhAdv_smallRows_le is the earliest substantive
statistical algebra dependency. Earlier advice/encoding admissions are routine serialization
and already have a separate candidate stream. This bound handles ALL response counts d and
row counts 0/1/2, independently of the canonical DLIN column reduction.

SelfReduction.mddhAdv_le still needs the different rank law of the special DLIN A0 and its
augmented matrix plus hybrid/averaging/realiser assembly; it is not silently treated as
proved by this small-row theorem. Its direct 4d/p already includes zero diagonals. No such
slack is added here or double-counted in any direct MDDH bound.

## Exact skeleton decomposition

H pp M U is the actual MDDH distinguisher acceptance probability over its existing machine
coins on the actual typed challenge with group matrices expMat(g,M), expMat(g,U). This is a
local bounded test, not an algorithm, inverse encoding or scalar-witness construction.
P(pp,M)=E_U H(pp,M,U), Q(pp,M)=E_S H(pp,M,M*S).

good(pp,M) is EXACTLY Function.Surjective(Matrix.mulVec M), the scalar column map K² -> K^ell.
It is not an opaque rank assertion or a new hypothesis in the frozen main theorem.

Explicit remaining holes:

1. hUniform: for each actual M with that surjective column map, P=Q. This is the uniform
   image law for the whole coefficient matrix (all response columns), not merely agreement
   of one scalar statistic. It applies even at d=0 and ell=0. A proposed independent generic
   helper target below could discharge it by symmetry; no helper proof was written.
2. hFailure: the uniform M's bad-surjectivity indicator has expectation ≤2/order(pp).
   This MUST use the existing hℓ κ : ell≤2. Generic field/cardinality counterpart is proposed
   for native search below. The hole is substantial; no rank probability is asserted as
   already proved.

Filled assembly:

* hP0/1 and hQ0/1 use expect_nonneg/mono/const with actual prob_nonneg/prob_le_one.
* hEntry is zero on good by hUniform and at most one on bad from the range bounds.
* abs_expect_sub_le_expect averages hEntry over the common uniform base M; hFailure gives
  the exact 2/p upper bound.
* A second averaging over actual publicParamsGen gives hAverage. hLoss reads
  publicParamsGen/core, expect_bind/map/const and G.inst_eq to identify its RHS with the
  frozen generator-coin average, without fixed schedules or desc injectivity.
* Actual mddhAdv/game/sample and probability readers identify false/true games with P/Q,
  integrating out their respective unused S/U draws. No game syntax equality is claimed.

All local :=?_ subproofs include swap for the root-verified goal ordering convention.
The two substantive holes remain term sorries; no new generic helper proof was supplied.

## Proposed helper headers / pending native probes

MddhSmallRows.helper-targets.lean.inc contains TWO SEARCH-ONLY headers:

* expect_sample_matrix_mul_of_mulVec_surjective: for any finite field K and known M with
  surjective column map, the uniform image of S under M*S has the uniform output average,
  for ANY real-valued test F. Arbitrary inner dimension m makes it adaptable to later
  column/row distribution arguments by standard transpose readers; no ad-hoc group API.
* smallRows_surjectivity_failure_le: for uniform r×2 field matrices, r≤2, bad-map probability
  ≤2/cardK. The probability form converts to hFailure using prob_eq_expect and classical
  conditionals, then ZMod.card. No new row-count or positivity assumption is added.

Suggested cycle-free home MatrixDH/FiniteLinear.lean imports generic scalar/probability APIs,
not MatrixDH.Defs/Linear/SelfReduction. Root must run native typing/exact?/apply? before ANY
new helper proof. The probe JSON explicitly excludes admitted consumer theorems. No source
or helper has been installed in the live tree by this agent.

## Static reuse search and nearest exact APIs

Read all of SelfReduction.lean:1-280, its declared main dependency/proof route, and current
Defs.lean:118-end. Searched remaining sorry locations and rank/surjectivity declarations.

Games/Foundations semantic searches covered sample-surjective/uniform-image/linear-expectation
and bad-event averaging. No complete probability-level uniform surjective-linear-image or
small-row rank-failure theorem was found. A nonexistent Games/UniformPushforward.lean path
was checked and corrected by actual file inventory; no inference relies on that missing file.
Existing sufficient assembly APIs are Probability.expect_nonneg/mono/const,
abs_expect_sub_le_expect; Bridges.expect_sample_pair; OneWay.uprob_eq_one_div_card for point
probabilities. Games.Hopping's abs_prob_sub_le_of_agree compares events on one computation,
not the needed whole-matrix linear-image law. No Closeness import is proposed.

Nearest Mathlib algebra/counting APIs, located and read:

* LinearAlgebra/Matrix/NonsingularInverse.lean:322,
  Matrix.mulVec_surjective_iff_exists_right_inverse; :340, mulVec_surjective_iff_isUnit.
  These supply the surjectivity/right-inverse characterization, including square case.
* LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:35, card_linearIndependent;
  :82, Matrix.card_GL_field. Read :37-75 and module imports. This avoids re-proving the
  generic finite-field GL count for the two-row failure probability.
* LinearAlgebra/Isomorphisms.lean:35/41, LinearMap.quotKerEquivRange /
  quotKerEquivOfSurjective; :51, its apply_mk reader. These are nearest kernel/fiber
  isomorphisms for uniform images. No new generic fiber cardinality proof is supplied.
* Finset big-operator fiberwise sum/cardinality APIs were found as lower-level alternatives
  (sum_card_fiberwise_eq_card_filter, card_eq_sum_card_fiberwise); do not privately rederive
  finite-fiber summation when filling the uniform-image subgoal.
* Matrix.mul_apply and existing Matrix.mulVec/vecMul associativity/readers remain the only
  intended entry-level algebra. No scalar exponent of an arbitrary group input is recovered.

Some initial broad rg outputs were truncated; the exact narrower source ranges above were
then read. An attempted LinearAlgebra/Matrix/Mul.lean path does not exist; matrix multiply
readers are Data/Matrix/Mul.lean. No native helper search or statement typing has been run.

## Risks / honest limits

The skeleton's two holes are the essential missing mathematics; range bounds and probability
reader assembly do not discharge them. The proposed helper headers are unverified and may
need precise import/type elaboration repairs before root's reuse searches. Their mathematical
claims are standard finite-field facts and appear sound, including zero dimensions, but no
proof/audit pass is claimed. Main skeleton native focus is dependent test/matrix type inference
and repeated expectation normalization; substantive future work focuses on uniform fibers and
existing GL cardinality specialization rather than copied private counting proofs.

## Final narrow source checks

A final search for uniformOfFintype/map/surjective and uniformOfFinset/map combinations in
Mathlib/Probability found no directly matching theorem in the inspected scope. No PMF or
measure-level theorem is claimed as a ProbComp reader. Re-read GeneralLinearGroup/Card:23-42
and :78-87: card_linearIndependent and Matrix.card_GL_field return Nat.card and explicit
products `(q^n-q^i)`, so a future failure proof should use the published cardinal conversion/
subtype equivalence rather than assume a probability formula already exists. These are
static API inspections, not native reuse searches or proof execution.
