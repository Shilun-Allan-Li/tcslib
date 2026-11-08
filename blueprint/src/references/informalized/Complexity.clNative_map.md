<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Encoded Payload Map

**Claim.** If $g$ is polynomial-time computable, then the function that decodes an input as $(a,b)$ and returns the encoding of $(a,g(b))$, or the empty string when decoding fails, is polynomial-time computable.

**Proof.** Take a machine computing $g$ in time $C(n+1)^e$. This time bound is monotone in the input length, so the machine construction for applying $g$ to the second component of an encoded pair applies. It produces a machine for the stated map with time bound $a(n+1+C(n+1)^e)$ for some constant $a$. To put this in polynomial form, set $m=n+1$. Since $m\geq 1$, both $m\leq m^{e+1}$ and $m^e\leq m^{e+1}$. Thus $m+Cm^e\leq (C+1)m^{e+1}$, giving the polynomial bound $a(C+1)(n+1)^{e+1}$.

**Key facts.** `Turing.FinTM.computesFunInTime_pairMapSnd`, `Turing.FinTM.ComputesInTime.mono`.
