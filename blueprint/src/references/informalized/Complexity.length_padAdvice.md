<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.length_padAdvice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Padded Circuit Advice

**Claim.** If the circuit encoding has length at least one less than the bound $A(n)$, then the padded advice string has length exactly $A(n)$.

**Proof.** Write $m$ for the length of the circuit encoding and $N=A(n)$. The padding appends one true bit and then $N-m-1$ false bits. Since $m+1\le N$, this replicate count is nonnegative, and the resulting length is $m+1+(N-m-1)=N$.
