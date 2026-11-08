<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.chooseFactor_leadingCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading Coefficient of a Falling Factorial

**Claim.** The leading coefficient of the falling-factorial polynomial normalized by $1/k!$ is $1/k!$, including the empty-product case $k=0$.

**Proof.** The descending Pochhammer polynomial is monic, so its leading coefficient is $1$. The leading coefficient of a product of nonzero polynomials is the product of their leading coefficients, and a constant polynomial has its constant as leading coefficient. Therefore multiplying the descending Pochhammer polynomial by the constant $1/k!$ gives leading coefficient $(1/k!)\cdot 1=1/k!$.
