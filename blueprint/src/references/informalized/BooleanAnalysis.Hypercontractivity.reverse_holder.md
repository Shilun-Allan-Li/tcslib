<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Holder.lean :: BooleanAnalysis.Hypercontractivity.reverse_holder -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reverse Hölder inequality

**Claim.** For $p<1$ with $p\ne0$ and nonnegative functions $f,g$ on the Boolean cube, $\langle f,g\rangle\ge M_p(f)M_{p/(p-1)}(g)$.

**Proof.** Split according to the sign of $p$. If $0<p<1$, the positive-exponent reverse Hölder inequality applies directly with exponent $p$. If $p<0$, its conjugate exponent $s=p/(p-1)$ satisfies $0<s<1$. Apply the positive-exponent result with exponent $s$ to the pair $(g,f)$. Since $s/(s-1)=p$, this gives $\langle g,f\rangle\ge M_s(g)M_p(f)$. Symmetry of the inner product and commutativity of multiplication give the stated inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.reverse_holder_of_pos`, `BooleanAnalysis.innerProduct_comm`.
