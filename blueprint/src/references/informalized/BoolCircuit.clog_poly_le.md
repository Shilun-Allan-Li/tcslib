<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.clog_poly_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Polynomial Bound

**Claim.** For all natural numbers $a$, $k$, and $m$, the base-$2$ ceiling logarithm satisfies $\operatorname{clog}_2\!\bigl(a(m+1)^k\bigr)\le a+k\bigl(\operatorname{log}_2(m)+1\bigr)$.

**Proof.** By the defining characterization of the ceiling logarithm, it suffices to show that $a(m+1)^k\le 2^{a+k(\operatorname{log}_2(m)+1)}$. The standard logarithm bounds give $a\le 2^a$ and $m+1\le 2^{\operatorname{log}_2(m)+1}$. Raising the latter inequality to the $k$th power and multiplying the two bounds yields $a(m+1)^k\le 2^a\bigl(2^{\operatorname{log}_2(m)+1}\bigr)^k$. The exponent laws identify the right-hand side with $2^{a+k(\operatorname{log}_2(m)+1)}$, as required.
