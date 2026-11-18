# Root-only exact?/apply? statements

No probes were executed. No NEW public helper is proposed; the following are existing
headers or local-claim shapes. Parent can probe them individually under the authorized
Lean check route. All are inside namespace TCSlib.Cryptography.Pairing.BilinearGroup,
with {ι κ υ : Type*}, {wG wT:ℕ}, B:BilinearGroup wG wT and standard imported instances.
Use `exact?` and `apply?` only in parent-controlled scratch; no theorem should be admitted
or weakened when testing alternatives.

Existing source bridge:

    [Fintype ι] (g : B.G) (a b : ι → ZMod B.order) :
      groupDot (B.expVec g a) b = g ^ (dotProduct a b).val

Existing GT bridge:

    [Fintype ι] (gT : B.GT) (a b : ι → ZMod B.order) :
      groupDot (B.expVecT gT a) b = gT ^ (dotProduct a b).val

Local hCoordinate (nearest result: pow_val_mul after pow_mul and expVec_apply):

    (g : B.G) (a b : ι → ZMod B.order) (i : ι) :
      (B.expVec g a i) ^ (b i).val = g ^ (a i * b i).val

Local hSum (nearest result: map_sum + toMul_sum for the explicit exponentMap):

    [Fintype ι] (g : B.G) (a b : ι → ZMod B.order) :
      g ^ (dotProduct a b).val = ∏ i, g ^ (a i * b i).val

Matrix target shapes are exactly the headers in each `.proof.lean.inc`. Probe source
bridge first, then expMat_mulVec and expVec_vecMul. Once bridge exists the remaining
matrix targets should be solved by the supplied pointwise reader chains; do not add a
second generic finite-product theorem.

Names to check for availability in parent context: map_sum, toMul_sum, Finset.prod_congr,
Matrix.mul_apply', dotProduct_comm, pow_mul, ZMod.val_zero. `map_sum` and `toMul_sum` are
GLOBAL names in the pinned Mathlib version; neither is a namespaced invented lemma.
