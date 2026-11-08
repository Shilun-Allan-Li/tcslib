<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.P_subset_PAdvicePoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time with Advice

**Claim.** Every binary language decidable in polynomial time is decidable in polynomial time when supplied with polynomial-length advice.

**Proof.** Let $L \in \mathsf{P}$. The zero-advice characterization of polynomial time says that $L$ lies in the union, over polynomial exponents, of the classes with advice bound identically zero (\(\texttt{Complexity.iUnion\_DTIMEAdvice\_zero\_eq\_P}\)). Hence for some exponent, a machine decides $L$ with an advice function whose length is zero at every input length. The general inclusion of each polynomial-time advice class in the union defining polynomial time with polynomial advice (\(\texttt{Complexity.DTIMEAdvice\_subset\_PAdvicePoly}\)) then places $L$ in that class, taking the advice-length polynomial to be zero.

**Key facts.** `Complexity.iUnion_DTIMEAdvice_zero_eq_P`, `Complexity.DTIMEAdvice_subset_PAdvicePoly`.
