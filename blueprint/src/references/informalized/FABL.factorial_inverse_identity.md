<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.factorial_inverse_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Reciprocal Identity

**Claim.** For natural numbers $j,k$ with $k\le j$, $(k!)^{-1}((j-k)!)^{-1}=\binom{j}{k}(j!)^{-1}$.

**Proof.** The factorial identity $\binom{j}{k}k!(j-k)!=j!$ holds when $k\le j$ (the factorial form of the binomial coefficient identity). All factorials are nonzero, so rearranging this equality by division gives $(k!)^{-1}((j-k)!)^{-1}=\binom{j}{k}(j!)^{-1}$.
