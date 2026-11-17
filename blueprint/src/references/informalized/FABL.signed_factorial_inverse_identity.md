<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.signed_factorial_inverse_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Factorial Inverse Identity

**Claim.** For $k\le j$, the signed product of reciprocal factorials equals $(-1)^j\binom{j}{k}/j!$.

**Proof.** Regroup the left-hand side as $(-1)^k(-1)^{j-k}$ multiplied by $(k!)^{-1}((j-k)!)^{-1}$. The factorial inverse identity (\texttt{FABL.factorial\_inverse\_identity}) replaces the latter product by $\binom{j}{k}(j!)^{-1}$. Finally, since $k+(j-k)=j$, the two powers of $-1$ multiply to $(-1)^j$, yielding the result.

**Key facts.** `FABL.factorial_inverse_identity`.
