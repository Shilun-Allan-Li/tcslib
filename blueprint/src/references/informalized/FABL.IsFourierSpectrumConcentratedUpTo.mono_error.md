<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.IsFourierSpectrumConcentratedUpTo.mono_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the Error Bound

**Claim.** If the sum of squared Fourier coefficients above cutoff $k$ is at most $\varepsilon$, then it is also at most any $\varepsilon'\ge\varepsilon$.

**Proof.** The quantity in question is at most $\varepsilon$ by hypothesis, and $\varepsilon\le\varepsilon'$. Transitivity of the order gives the desired upper bound.
