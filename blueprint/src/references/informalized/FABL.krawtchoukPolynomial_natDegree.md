<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukPolynomial_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Krawtchouk polynomial

**Claim.** For natural numbers $n$ and $j$ with $j\le n$, the natural degree of the Krawtchouk polynomial $K_{n,j}$ is $j$.

**Proof.** Each summand in the defining sum has natural degree $j$ (the summand-degree calculation, `krawtchoukSummand_natDegree`). Therefore the degree of the sum is at most $j$. To show it is not smaller, compute its coefficient in degree $j$. For each summand, degree exactly $j$ means its coefficient of $X^j$ is its leading coefficient. Summing these leading coefficients gives $(-1)^j2^j/j!$ (the leading-coefficient sum, `sum_krawtchoukSummand_leadingCoeff`), which is nonzero. Thus the sum has a nonzero coefficient in degree $j$, so its natural degree is at least $j$. Together the two bounds give natural degree exactly $j$.

**Key facts.** `FABL.krawtchoukSummand_natDegree`, `FABL.sum_krawtchoukSummand_leadingCoeff`.
