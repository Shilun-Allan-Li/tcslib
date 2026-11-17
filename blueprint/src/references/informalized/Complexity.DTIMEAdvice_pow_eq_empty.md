<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.DTIMEAdvice_pow_eq_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-Power Advice Classes Are Empty

**Claim.** For every nonzero natural number $c$ and every advice-length function $a$, the class $\mathrm{DTIMEAdvice}(n\mapsto n^c,a)$ is empty.

**Proof.** Since $c\ne0$, the natural-number power $0^c$ is zero. Apply the zero-time emptiness result (`Complexity.DTIMEAdvice_eq_empty_of_eq_zero`) to the time function $n\mapsto n^c$, whose value at zero is therefore zero. This gives the claimed empty class.

**Key facts.** `Complexity.DTIMEAdvice_eq_empty_of_eq_zero`.
