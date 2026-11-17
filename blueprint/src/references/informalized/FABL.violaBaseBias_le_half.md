<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaSeedLength.lean :: FABL.violaBaseBias_le_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Base Bias

**Claim.** For $0\le\varepsilon\le1$ and every natural number $d$, the base bias $(\varepsilon/9)^{2^{\max(d-1,0)}}$ is at most $1/2$.

**Proof.** The base $\varepsilon/9$ is nonnegative and at most $1/9$, hence at most $1$. The exponent $2^{d-1}$ (with natural subtraction in the exponent) is at least $1$. For a base in $[0,1]$, raising it to an exponent at least $1$ cannot increase it, so the base bias is at most $\varepsilon/9$. Finally, $\varepsilon\le1$ gives $\varepsilon/9\le1/9\le1/2$, proving the bound.
