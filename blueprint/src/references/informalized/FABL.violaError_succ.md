<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.violaError_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Viola Error Identity

**Claim.** For $0\leq\varepsilon\leq1$ and $d\geq1$, the Viola error satisfies $V(\varepsilon,d+1)=3\sqrt{V(\varepsilon,d)}$.

**Proof.** Since $d\geq1$, we have $d-1+1=d$, so $(2)^d=2^{d-1}\cdot2$. Consequently, the exponent $1/2^d$ equals $(1/2^{d-1})/2$. For nonnegative $\varepsilon$, taking a square root of $\varepsilon^{1/2^{d-1}}$ therefore gives $\varepsilon^{1/2^d}$, by the multiplication law for real powers. In the definition of $V$, the exponent at depth $d+1$ is $1/2^d$; also, $\sqrt{9x}=3\sqrt{x}$ for $x\geq0$. Substituting these identities yields $V(\varepsilon,d+1)=3\sqrt{V(\varepsilon,d)}$.
