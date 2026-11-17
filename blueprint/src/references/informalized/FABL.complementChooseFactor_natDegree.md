<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.complementChooseFactor_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Complemented Falling Factorial

**Claim.** The real polynomial obtained by dividing the product of the factors $n-X-j$, for $0\le j<k$, by $k!$ has degree $k$.

**Proof.** The scalar $1/k!$ is nonzero, so multiplying by it does not change the degree. The falling-factorial polynomial has degree k, and the complemented linear polynomial $n-X$ has degree one (`FABL.complementLinear_natDegree`). The degree of a composition is the product of the degrees in this setting, so the composed polynomial has degree $k\cdot1=k$.

**Key facts.** `FABL.complementLinear_natDegree`.
