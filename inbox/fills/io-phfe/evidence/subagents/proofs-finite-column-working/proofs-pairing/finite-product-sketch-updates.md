# Suggested proof-sketch-only refresh

These are OPTIONAL proof-route prose updates accompanying the candidate bodies. They do not
alter theorem headers or source-derived opening prose. Keep the frozen-statement check's
published sketch exemption and record the proof-route refresh in the proof commit.

For groupDot_expVec, replace its existing **Proof sketch.** paragraph with:

**Proof sketch.** Define the local exponentMap into Additive G using the published modular
addition law. Use map_sum and toMul_sum for hSum. Obtain hCoordinate from expVec_apply,
pow_mul and pow_val_mul, then combine both through groupDot_eq and Finset.prod_congr.

For groupDot_expVecT:

**Proof sketch.** Define the local exponentMap into Additive GT using pow_val_add_GT.
Use map_sum and toMul_sum for hSum, and expVecT_apply/pow_val_mul_GT for hCoordinate.
Finish through groupDot_eq and Finset.prod_congr; no finite-product theorem is re-proved.

For pair_expVec, a closer sketch is:

**Proof sketch.** Read pairVec_eq and the two expVec coordinates, then use bilinear_pow
and pow_mul pointwise. The product is groupDot of the target implicit vector; apply the
already proved groupDot_expVecT finite-product bridge.
