<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Extension.lean :: BooleanAnalysis.Hypercontractivity.reverse_bonami_beckner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reverse Bonami–Beckner inequality

**Claim.** Under the stated parameter conditions, every nonnegative function on the Boolean cube satisfies $M_q(T_\rho f)\ge M_p(f)$.

**Proof.** Apply the extension theorem for reverse Bonami–Beckner (`extend_reverse_bonami_beckner`) with the given parameters and function. Its hypotheses are exactly $q<1$, $q\le p\le1$, $0\le\rho\le1$, and $\rho^2\le(1-p)/(1-q)$, together with nonnegativity of $f$. It gives the asserted comparison of the extended power means.

**Key facts.** `BooleanAnalysis.Hypercontractivity.extend_reverse_bonami_beckner`.
