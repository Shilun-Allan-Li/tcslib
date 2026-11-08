<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.uniformProbability_eq_add_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement and Disagreement Probabilities

**Claim.** For sign-valued functions $f,g$ on the Boolean cube, the uniform probabilities that they agree and disagree sum to $1$.

**Proof.** At each input, exactly one of the statements $f(x)=g(x)$ and $f(x)\ne g(x)$ holds. Consequently, the two indicator functions for agreement and disagreement add to the constant function $1$. Uniform expectation is additive, and the uniform expectation of the constant $1$ is $1$. Taking expectations gives the claimed identity.
