<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityNoiseStability.lean :: FABL.noiseStability_majority_next_odd_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Odd Majority Stability

**Claim.** For $0<\rho<1$, the noise stability of majority on $2m+3$ coordinates is at most its noise stability on $2m+1$ coordinates.

**Proof.** Apply the non-strict part of the odd-majority comparison theorem (`noiseStability_majority_next_odd_comparison`) at $m$ and the given correlation parameter. Its first conclusion is exactly the claimed inequality.

**Key facts.** `FABL.noiseStability_majority_next_odd_comparison`.
