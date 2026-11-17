<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.f₂DotProduct_bentDualFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual frequency under a linear change

**Claim.** For an invertible linear map $M$ on $\mathbb{F}_2^n$, the dot product of the bent dual frequency of $\gamma$ with $y$ equals the dot product of $\gamma$ with $M^{-1}y$.

**Proof.** The dot product pairing identifies each vector with the linear functional obtained by pairing against it. By definition, the bent dual frequency is the vector corresponding to the functional obtained from the functional of $\gamma$ by composing with $M^{-1}$. Evaluating that functional at $y$ gives the functional of $\gamma$ evaluated at $M^{-1}y$, which is the asserted dot product.
