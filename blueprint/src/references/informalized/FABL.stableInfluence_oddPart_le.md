<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.stableInfluence_oddPart_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Part Stable Influence Bound

**Claim.** For $\rho\in[0,1]$, the stable influence of the odd part of $f$ at coordinate $i$ is at most the stable influence of $f$ there.

**Proof.** Compare the two stable-influence sums term by term over subsets $S$ containing $i$, splitting according to whether $|S|$ is even or odd. If $|S|$ is even, the Fourier coefficient of the odd part vanishes (\texttt{fourierCoeff_oddPart_of_even}); the corresponding summand is therefore zero, while the summand for $f$ is nonnegative because $\rho\ge0$ and it contains a square. If $|S|$ is odd, the Fourier coefficient of the odd part equals that of $f$ (\texttt{fourierCoeff_oddPart_of_odd}), so the summands agree. Summing these termwise comparisons proves the bound.

**Key facts.** `FABL.fourierCoeff_oddPart_of_even`, `FABL.fourierCoeff_oddPart_of_odd`.
