<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.fieldDegree_eq_of_dyadic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field Degree for Dyadic Bias

**Claim.** If the dimension is $2^{d-r}$, the numerator is $1$, the denominator is $2^r$, and $r\leq d$, then the field degree is $d$.

**Proof.** Under these assumptions, the scale is the ceiling quotient of $2^{d-r}2^r$ by $1$. The product is $2^d$, and division by $1$ leaves the scale equal to $2^d$. The field degree equals the base-$2$ ceiling logarithm of the scale (`SmallBiasInput.fieldDegree_eq_clog`). The ceiling logarithm of $2^d$ is $d$, so the field degree is $d$.

**Key facts.** `FABL.SmallBiasInput.fieldDegree_eq_clog`.
