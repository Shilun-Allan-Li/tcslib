<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.fourierCoeff_oddPart_of_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-degree coefficients vanish

**Claim.** If $S$ has even cardinality, then the Fourier coefficient at $S$ of the odd part of $f$ is zero.

**Proof.** Use the odd-part coefficient formula (`fourierCoeff_oddPart`) to write the coefficient as $(1-(-1)^{|S|})\widehat f(S)/2$. Since $|S|$ is even, $(-1)^{|S|}=1$, so the factor in parentheses is zero. Hence the coefficient vanishes.

**Key facts.** `FABL.fourierCoeff_oddPart`.
