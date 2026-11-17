<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.abs_measureReal_sub_le_symmDiff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Difference of Finite Set Measures

**Claim.** For a finite measure $\mu$, the absolute difference between the real measures of $C$ and $D$ is at most the real measure of their symmetric difference.

**Proof.** The measure of $C$ is at most the measure of $C\mathbin{\triangle}D$ plus the measure of $D$, by the symmetric-difference measure inequality applied with the third set empty. Exchanging $C$ and $D$ gives the reverse bound, since symmetric difference is commutative. These two inequalities bound both signs of $\mu(C)-\mu(D)$, and hence its absolute value.
