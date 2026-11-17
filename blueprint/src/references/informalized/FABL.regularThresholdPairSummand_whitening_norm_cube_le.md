<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPairSummand_whitening_norm_cube_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Whitened Summand Norm Bound

**Claim.** After whitening, the cube of the summand's norm is bounded by the stated same-sign or opposite-sign expression, according as the coordinate signs agree or differ.

**Proof.** Split into the two possibilities for the signs at coordinate $i$. If they agree, rewrite the summand as the vector with both entries equal to $\mathrm{signValue}(x_i)a_i$. The whitening bound for equal signs (`FABL.bentkusWhitening_norm_sameSigns_le`) gives a norm at most $\sqrt{2}|a_i|/\sqrt{1+\rho}$. If they differ, since both are signs, the second sign is the negative of the first. Rewrite the summand as the vector with entries $\mathrm{signValue}(x_i)a_i$ and its negative. The whitening bound for opposite signs (`FABL.bentkusWhitening_norm_oppositeSigns_le`) gives a norm at most $\sqrt{2}|a_i|/\sqrt{1-\rho}$. In either case, both sides of the norm bound are nonnegative, so cubing preserves the inequality and yields the claimed bound.

**Key facts.** `FABL.bentkusWhitening_norm_sameSigns_le`, `FABL.bentkusWhitening_norm_oppositeSigns_le`.
