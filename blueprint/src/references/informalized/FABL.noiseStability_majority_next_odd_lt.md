<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityNoiseStability.lean :: FABL.noiseStability_majority_next_odd_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Decrease for Consecutive Odd Majorities

**Claim.** For every $m\ge 0$ and $0<\rho<1$, the noise stability of majority on $2m+3$ coordinates is strictly less than that on $2m+1$ coordinates.

**Proof.** Since $0<\rho<1$, the comparison theorem applies with $\rho$ in the half-open interval $[0,1)$. Its strict conclusion says that whenever $\rho>0$, the stability at the next odd size is strictly smaller than at the current odd size. Applying that conclusion at $m$ gives the result.

**Key facts.** `FABL.noiseStability_majority_next_odd_comparison`.
