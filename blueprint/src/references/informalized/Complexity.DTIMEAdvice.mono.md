<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.DTIMEAdvice.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Time with Advice

**Claim.** If $T_1(n)\le T_2(n)$ for every $n$, then $\mathrm{DTIMEAdvice}(T_1,A)\subseteq\mathrm{DTIMEAdvice}(T_2,A)$.

**Proof.** Take a language in $\mathrm{DTIMEAdvice}(T_1,A)$, witnessed by a constant $c$, an advice function $\alpha$, and a machine $M$. Keep these witnesses, including the advice-length condition. For each input $x$, the bound on the time functions yields $cT_1(|x|)\le cT_2(|x|)$. Applying monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) to the computation on the advice-encoded input transfers the decision guarantee to the larger time bound. The advice function and its length are unchanged, so the language belongs to $\mathrm{DTIMEAdvice}(T_2,A)$.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
