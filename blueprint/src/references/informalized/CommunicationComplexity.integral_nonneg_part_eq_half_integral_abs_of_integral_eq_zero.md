<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive part and the $L^1$ norm

**Claim.** If an integrable measurable function has mean zero, its integral over the set where it is nonnegative equals half the integral of its absolute value.

**Proof.** Let $A=\{x:g(x)\ge 0\}$. This is measurable because $g$ is measurable. Splitting the zero integral over $A$ and its complement gives $\int_A g\,d\mu+\int_{A^c}g\,d\mu=0$. On $A$, $|g|=g$; on $A^c$, $|g|=-g$. Thus the integral of $|g|$ over the whole space is $\int_A g\,d\mu-\int_{A^c}g\,d\mu$. The zero-mean identity says the second term is $-\int_A g\,d\mu$, so this total is $2\int_A g\,d\mu$. Rearranging proves the claim.
