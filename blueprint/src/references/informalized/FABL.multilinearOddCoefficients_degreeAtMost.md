<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.multilinearOddCoefficients_degreeAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for Odd Coefficients

**Claim.** If the coefficient function vanishes on every subset of size greater than $k+1$, then adjoining position $0$ to the shifted subset produces coefficients that vanish whenever the original subset has size greater than $k$.

**Proof.** Let $S$ have size greater than $k$. The shifted subset does not contain $0$, so adjoining $0$ increases its cardinality by exactly one. Shifting preserves cardinality, and therefore the subset used to define the new coefficient has size $|S|+1>k+1$. The assumed degree bound makes its coefficient zero, which is precisely the new coefficient at $S$.

**Key facts.** `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`.
