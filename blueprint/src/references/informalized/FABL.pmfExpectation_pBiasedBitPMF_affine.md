<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_pBiasedBitPMF_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Biased Bit

**Claim.** For a bit that is true with probability $\delta$ and false with probability $1-\delta$, the expectation of $g$ is $(1-\delta)g(\mathrm{false})+\delta g(\mathrm{true})$.

**Proof.** Write the value of $g$ at either bit as $g(\mathrm{false})+(g(\mathrm{true})-g(\mathrm{false}))I$, where $I$ is $0$ on false and $1$ on true. By linearity of expectation, the expectation is $g(\mathrm{false})+(g(\mathrm{true})-g(\mathrm{false}))\mathbb E[I]$. The indicator has expectation $\delta$ (`pmfExpectation_pBiasedBitPMF_zeroOneValue`), so rearranging gives the formula.

**Key facts.** `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_pBiasedBitPMF_zeroOneValue`.
