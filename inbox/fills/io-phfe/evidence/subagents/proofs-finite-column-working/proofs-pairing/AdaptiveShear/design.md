# Minimal adaptive public-preserving shear target

HEADER ONLY. `helper-target.lean` supplies one new algebra theorem as a term-admitted native
probe target, with no proof/tactic block and no source edit. Root must first typecheck and run
isolated exact?/apply? probes; no proof of this helper has been attempted.

## Proposed cycle-free home and imports

Proposed live home, subject to root's scope judgment:
`TCSlib/Cryptography/Pairing/MatrixDH/AdaptiveShear.lean`, namespace
`TCSlib.Cryptography.Pairing`. It imports only the four precise Mathlib roots shown in the
probe. It imports no Pairing group/facade, FE, garbling, game, simulator or source theorem.
`LinearSecurity/Theorems.lean` can import it directly, without a reverse dependency or cycle.

It is an existence/equality lemma, not a public runtime def, sampler, state interface, game
abstraction or replacement of the frozen target. No new efficient witness or group-to-scalar
operation is proposed. No additional matrix theorem is proposed because the required matrix
identities are already public Mathlib laws.

## Exact abstract meaning and existing constructors

For fixed latent u, the map is x |-> x + shift u (projection x). The only hypothesis says the
shift lies in the additive projection's kernel. Thus projection is unchanged and the inverse
can read the SAME original public projection and unchanged u before subtracting the shift.
Neither injectivity nor surjectivity of projection is assumed. No finite-type, inhabitedness,
choice, prime-order or dimension condition is needed; finite uniform reindexing is the later
caller's existing `ProbComp.expect_sample_equiv` application.

The intended reuse route is entirely existing equivalence machinery:

- In each fiber `projection x = p`, restrict `Equiv.addRight (shift u p)` with the public
  `Equiv.subtypeEquiv` API. Its predicate equivalence is just AddMonoidHom.map_add and hshift.
- `Equiv.ofFiberEquiv` assembles those fiber permutations; its public `ofFiberEquiv_map` already
  gives projection preservation, so do not re-prove a generic fiber-preservation theorem.
- `Equiv.prodCongrRight` assembles the family in u and preserves u. `prodShear` with refl is an
  equivalent existing constructor; do not write a new product/shear definition.
- `Equiv.coe_addRight`, addRight_symm and sub_eq_add_neg identify the explicit forward/inverse
  formulas. The helper only packages their useful joint statement for the existing adaptive hop.

The forward formula itself fixes the first coordinate; the third conjunct fixes the public
projection of the second. An arbitrary challenge selector `choose u (projection x)` is then
unchanged by ordinary congruence, so a separate selector-invariance helper would be redundant.
The selector may return Option challenge, with zero shifts in the no-challenge branch; the
abstract theorem does not incorrectly require an adversary to make a challenge.

## Specialization to the actual matrix shear

Fix pp, A, c, adversary coins and all unaffected tape coordinates. Let B=A^T, a be the final
inverse-basis column on the good basis event, so B*vec a=0 and dot c a=1. Use:

- latent U: the unchanged public-variable scalar matrix;
- E: the product of W and V matrix spaces;
- P: the product of the B*W and B*V public projection matrix spaces;
- projection: the product map from the two existing Matrix.addMonoidHomMulLeft B homs;
- challenge `(x*,z*)`: the actual adversary-selected challenge as a function of the fixed public
  data, B*U, and the two projection coordinates;
- shift U p:
  `(Matrix.vecMulVec a z*, Matrix.vecMulVec a ((Matrix.vecMul c U) vecMul X(x*)))`.

Here `X(x*)` is exactly the existing `PartialGarbling.publicTensor` with its existing index
shapes. The second component is c^T U followed by matrix X, not a recomputed or shifted U.
It has width Fin 2; W has private width zDim. Keep n' as the separate PG output width.
The source scalar matrix products use `*`; group-valued matrix products later use Hadamard.

No matrix helper is needed for hshift: Matrix.mul_add, Matrix.mul_vecMulVec, B*a=0,
Matrix.zero_vecMulVec and Matrix.add_zero are the exact public formulas. Likewise
Matrix.vecMul_add and Matrix.vecMul_vecMulVec, together with dot c a=1 and one_smul, give
`c^T W' = c^T W + z*` and `c^T V' = c^T V + ((c^T U) X(x*))` without another helper.
`Matrix.addMonoidHomMulLeft` already supplies the public-projection hom, so do not re-implement
matrix multiplication as an additive map.

The public MPK has A^T, B*W, B*U, B*V exponentiated. Equality of these scalar projections implies
identical group MPK by congruence; no injectivity of exponentiation and no exponent extraction
is needed. Before the first challenge, protocolHandler answers every key request with none;
therefore for fixed MPK/coins its refusal history and first challenge are identical, including
total-budget use and the possibility of returning without a challenge. This is why the actual
challenge selector factors through unchanged public data. A future deterministic replay lemma
may be useful, but should be proposed/searched separately; it is not part of this algebra target.

## Important complete-hop bookkeeping (not hidden in the helper)

The current gameHandler mode2 computes maskedCipher from c,W,U,V; mode3 uses simEncCore's
separately stored w,v and uses the separately stored globalUAt row. setupAt draws all those
blocks independently. Consequently the bare map changing W/V and leaving every other setup
coordinate untouched is NOT, by itself, a pointwise equality of the two full handlers.

The full source proof must first expose independent high/low coordinates using the invertible
H=(A|c)^T action. The low rows c^T W, c^T U, c^T V are uniform independently of B*W,B*U,B*V.
The unused w/v/global-U blocks can then be exchanged/reindexed with the appropriate low rows,
while retaining all unused coordinates so the transformation is a genuine bijection of the
complete padded tape. The triangular translation above acts on the retained low coordinates
and fixes their public projections; it does not justify silently identifying independent
existing block variables. This is bookkeeping still required in game2_game3_accept, not a
counterexample to its law equality and not a requested frozen-header change.

Per-query T coordinate reindexing should similarly use the existing invertible H column action
(via its linear equivalence/columnwise pi congruence), leaving the two projected rows fixed
and supplying the fresh low row. Existing uniform-equivalence and relational simulation laws
then handle all adaptive keys. Do not add a full-game helper that simply asserts the desired
acceptance equality or assumes the missing independence as a hypothesis.

## Relevant actual source boundaries

- LinearSecurity/Games.gameHandler: mode2 maskedCipher/decomposedKey; mode3 simEncCore/semiKey.
- LinearSecurity/Data.protocolHandler: prechallenge keys and repeated challenges refuse;
  accepted-key counter has the existing total-budget cap.
- Data.setupAt/globalUAt/keyAt/simKeyAt: explicit scalar tape block readers; all untouched
  padding must remain represented by the full-tape equivalence.
- LinearSimulator.simSetupCore_eq: MPK consists of A^T and B*W/B*U/B*V; inverse depends on A,c.
- LinearSecurity/Keys.projectedKey_eq/semiKey_eq: exact public/low-row matrix formulas.

No helper proof or Lean/lake/Git/native check has been run. All proposed syntax remains for
root's native typing and reuse probes before proof drafting.
