<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.IsFourierSpectrumConcentratedUpTo.mono_cutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the Degree Cutoff

**Claim.** If the sum of squared Fourier coefficients over sets of size greater than $a$ is at most $\varepsilon$, then for any $b\ge a$ the corresponding sum over sets of size greater than $b$ is also at most $\varepsilon$.

**Proof.** When $a\le b$, every set whose size is greater than $b$ also has size greater than $a$. Thus the sum of squared coefficients over the former collection is no greater than the sum over the latter collection (\texttt{fourierWeightAboveReal_antitone}). Combining this with the assumed bound at cutoff $a$ proves the bound at cutoff $b$.

**Key facts.** `FABL.fourierWeightAboveReal_antitone`.
