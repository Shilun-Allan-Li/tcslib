<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadLimitations.lean :: FABL.eq_one_on_pmf_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum attainment on the support

**Claim.** If a function is bounded above by $1$ and has expectation $1$ under a probability mass function on a finite set, then it equals $1$ at every point in the support.

**Proof.** Fix a support point $x$. The bound gives $g(x)\le 1$. Suppose instead that $g(x)<1$. Since $p(x)\ne0$, its real-valued weight is strictly positive. At every point $y$, the summand $(p(y)).toReal\,g(y)$ is at most $(p(y)).toReal$, and at $x$ it is strictly smaller. Summing over the finite set therefore gives $\mathbb E_p[g]<\mathbb E_p[1]$. The expectation of the constant function $1$ is $1$ (`pmfExpectation_const_one`), contradicting the assumed expectation of $g$. Thus $g(x)=1$.

**Key facts.** `FABL.pmfExpectation_const_one`.
