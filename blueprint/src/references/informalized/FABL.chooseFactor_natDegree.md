<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.chooseFactor_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Falling Factorial

**Claim.** The polynomial obtained by multiplying the falling-factorial polynomial of order $k$ by $1/k!$ has natural degree $k$, including the empty-product case $k=0$.

**Proof.** The descending Pochhammer polynomial of order $k$ has natural degree $k$. Multiplication by a nonzero constant preserves natural degree; here $1/k!$ is nonzero for every natural number $k$. Hence the normalized polynomial also has natural degree $k$.
