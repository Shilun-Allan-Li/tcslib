<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.complementChooseFactor_leadingCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading Coefficient of a Complemented Falling Factorial

**Claim.** The polynomial obtained by scaling the complemented falling factorial by $1/k!$ has leading coefficient $(-1)^k/k!$.

**Proof.** The leading coefficient of a product is the product of the leading coefficients, and a nonzero constant polynomial has its constant as leading coefficient. For the composed factor, the leading-coefficient formula for composition applies because the inner polynomial $n-X$ has degree one; its degree is confirmed by the companion fact about the complemented linear polynomial (`FABL.complementLinear_natDegree`). The outer falling-factorial polynomial is monic and has degree k. Consequently, its composition has leading coefficient $1\cdot(-1)^k$, since the inner polynomial has leading coefficient $-1$ (`FABL.complementLinear_leadingCoeff`). Multiplying by the scalar $1/k!$ gives $(-1)^k/k!$.

**Key facts.** `FABL.complementLinear_natDegree`, `FABL.complementLinear_leadingCoeff`.
