<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.DTIMEAdvice.mono_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the Time Bound with Advice

**Claim.** If $T_1(n)\le aT_2(n)$ for every $n$, then $\mathrm{DTIMEAdvice}(T_1,A)\subseteq\mathrm{DTIMEAdvice}(T_2,A)$.

**Proof.** Let a language in $\mathrm{DTIMEAdvice}(T_1,A)$ have witnesses $c$, advice function $\alpha$, and machine $M$. Use the same advice and machine, and replace the time constant by $ca$. For each input $x$, multiplying $T_1(|x|)\le aT_2(|x|)$ by $c$ gives $cT_1(|x|)\le c(aT_2(|x|))=(ca)T_2(|x|)$. The equality is associativity of multiplication. The machine’s computation within the original bound thus fits within the new bound by monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`). The advice-length condition remains intact.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
