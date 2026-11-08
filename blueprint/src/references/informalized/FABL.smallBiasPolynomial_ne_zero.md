<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasGenerator.lean :: FABL.smallBiasPolynomial_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the small-bias polynomial

**Claim.** If $\gamma\in\mathbb F_2^n$ is nonzero, then its small-bias polynomial is nonzero.

**Proof.** Because $\gamma$ is not the zero vector, some coordinate $i$ satisfies $\gamma_i\ne0$. The coefficient of the polynomial at degree $i+1$ is the image of $\gamma_i$ in the binary extension field. The field extension map is injective, so this coefficient is nonzero. A zero polynomial has every coefficient zero; hence the polynomial cannot be zero.
