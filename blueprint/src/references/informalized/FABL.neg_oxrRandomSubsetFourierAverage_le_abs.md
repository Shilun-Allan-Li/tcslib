<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.neg_oxrRandomSubsetFourierAverage_le_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Fourier average bound

**Claim.** For a random subset $K$ with the weights specified in the formal definitions, the negative signed Fourier average is at most the corresponding average of absolute Fourier coefficients.

**Proof.** Write each expectation as its finite weighted sum. The weights are nonnegative because the parameter $1-\delta$ lies in $[0,1]$; this follows from $0\leq\delta\leq1$ and the nonnegativity of the random-subset weights (`FABL.deltaRandomSubsetWeight_nonneg`). For each $K$, the negative of $(-1)^{|S\cap K|}\widehat f(S\cap K)$ is at most its absolute value. Multiplying by the nonnegative weight preserves the inequality. Since $|(-1)^{|S\cap K|}|=1$, that absolute value is exactly $|\widehat f(S\cap K)|$. Summing over $K$ proves the claimed comparison.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`.
