<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.fourierDegree_degreeTruncation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of Fourier truncation

**Claim.** The sum of the Fourier terms indexed by subsets of size at most $k$ has Fourier degree at most $k$.

**Proof.** By the degree characterization, it is enough to show that the truncated function has zero Fourier coefficient at each set $S$ with $|S|>k$ (`FABL.fourierDegree_le_iff`). Its coefficient at $S$ is the original coefficient if $|S|\le k$, and is zero otherwise (`FABL.fourierCoeff_degreeTruncation`). Here the latter case applies, so the required coefficient vanishes.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_degreeTruncation`.
