<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.theorem4_22_of_switchingFailureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration from a Switching Bound

**Claim.** If the probability that a random restriction leaves decision-tree depth at least $k$ is at most $\varepsilon/3$, then the Fourier spectrum is concentrated through degree $3k/\delta$ with error at most $\varepsilon$.

**Proof.** The restriction-to-concentration lemma states that, for $\delta>0$, $\delta\le1$, and positive integer $k$, the spectrum is concentrated through degree $3k/\delta$ with error $3$ times the switching failure probability (\texttt{lemma4\_21}). The assumed probability bound makes this error at most $3(\varepsilon/3)=\varepsilon$. Increasing the allowed error preserves Fourier concentration (\texttt{IsFourierSpectrumConcentratedUpTo.mono\_error}), yielding the claim.

**Key facts.** `FABL.lemma4_21`, `FABL.IsFourierSpectrumConcentratedUpTo.mono_error`.
