/-- Pairing a known exponent vector with an arbitrary source-group vector applies
its known scalar weights inside the pairing. This is technical implicit-representation
arithmetic for [Wee20, §2.1, p.4; §4.2, p.9]. No exponents of the arbitrary vector are
chosen.

**Proof sketch.** Read pairVec_eq, expVec_apply and groupDot_eq. The coordinate
identity is pair_pow_left, and map_prod for the existing monoid hom B.pair g moves
the product through the pairing. -/
theorem pairVec_expVec_left [Fintype ι] (g : B.G) (v : ι → ZMod B.order)
    (u : ι → B.G) :
    B.pairVec (B.expVec g v) u = B.pair g (groupDot u v) := by
  simp only [B.pairVec_eq, B.expVec_apply, groupDot_eq, map_prod,
    B.pair_pow_left, B.pair_pow_right]
