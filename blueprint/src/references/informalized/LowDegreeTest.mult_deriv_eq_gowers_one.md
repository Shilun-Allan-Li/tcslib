<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.mult_deriv_eq_gowers_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Gowers product formula

**Claim.** The multiplicative derivative of a Boolean function in direction $h$ at $x$ equals its order-one Gowers product at $x$ with direction $h$.

**Proof.** At order one, the recursive definition of the Gowers product gives the product of the function at the base point and at the base point XORed with the sole direction. This is precisely the definition of the multiplicative derivative, namely $f(x)f(x\oplus h)$.
