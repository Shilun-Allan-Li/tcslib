-- SEARCH-ONLY CANDIDATE STATEMENTS. Do not import these placeholders into probes.
-- Existing context: namespace TCSlib.Cryptography.Pairing.BilinearGroup;
-- {ι κ υ : Type*}; {wG wT : ℕ}; (B : BilinearGroup wG wT).
-- Root converts each statement to an anonymous exact?/apply? target independently.

/-- Pairing a known exponent vector with an arbitrary source-group vector applies
its known scalar weights inside the pairing. This is technical implicit-representation
arithmetic for [Wee20, §2.1, p.4; §4.2, p.9]. No exponents of the arbitrary vector are
chosen.

**Proof sketch.** Read pairVec_eq, expVec_apply and groupDot_eq. The coordinate
identity is pair_pow_left, and map_prod for the existing monoid hom B.pair g moves
the product through the pairing. -/
theorem pairVec_expVec_left [Fintype ι] (g : B.G) (v : ι → ZMod B.order)
    (u : ι → B.G) :
    B.pairVec (B.expVec g v) u = B.pair g (groupDot u v) := sorry

/-- Successive known scalar row/matrix weights on an arbitrary source-group matrix
compose by ordinary scalar matrix multiplication. This is technical implicit arithmetic
for [Wee20, §2.1, p.4; §4.2, p.9]. The group matrix remains arbitrary.

**Proof sketch.** Read groupVecMul_apply, matMulGroup_apply and groupDot_eq. Distribute
known powers over products, interchange the two finite products, use pow_val_mul to
combine known scalar weights, and use the modular additive exponent law to collect
each column's scalar sum. Reuse finite-product and scalar vecMul equations. -/
theorem groupVecMul_matMulGroup [Fintype ι] [Fintype κ]
    (v : ι → ZMod B.order) (W : Matrix ι κ (ZMod B.order))
    (M : Matrix κ υ B.G) :
    groupVecMul v (matMulGroup W M) = groupVecMul (Matrix.vecMul v W) M := sorry
