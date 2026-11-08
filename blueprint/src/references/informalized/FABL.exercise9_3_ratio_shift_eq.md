<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.exercise9_3_ratio_shift_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted factorial ratio identity

**Claim.** For nonnegative integers $m,d$, the ratio of the six-block multinomial coefficient to the square of the binomial coefficient equals $((3d)!)^2/(d!)^6$ times the shifted factorial ratio $R(m,d)$.

**Proof.** First rewrite $R(m,d)$ as $(m+3d)!^2/((m+6d)!\,m!)$, using the product formula for the shifted factorial ratio (`fixedShiftFactorialRatio_eq_factorial_ratio`). The six-block multinomial factorial identity gives $M(m+6d,d)(d!)^6m!=(m+6d)!$ (`sixBlockMultinomial_shift_mul_factorials`), while the binomial factorial identity gives $\binom{m+6d}{3d}(3d)!(m+3d)!=(m+6d)!$ (`choose_three_mul_shift_mul_factorials`). All factorials and the binomial coefficient here are nonzero, since factorials are positive and $3d\le m+6d$. Substitute these two identities and cancel the nonzero factors; the remaining equality is exactly the claimed ratio identity.

**Key facts.** `FABL.fixedShiftFactorialRatio_eq_factorial_ratio`, `FABL.sixBlockMultinomial_shift_mul_factorials`, `FABL.choose_three_mul_shift_mul_factorials`.
