<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.cast_choose_div_two_succs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-step binomial quotient identity

**Claim.** For natural numbers $m$ and $j$, $\binom{m}{j}/((j+1)(j+2))=\binom{m+2}{j+2}/((m+1)(m+2))$.

**Proof.** First separate the denominator on the left into successive divisions by $j+1$ and $j+2$. Apply the one-step binomial quotient identity (FABL.cast_choose_div_succ) to replace $\binom{m}{j}/(j+1)$ by $\binom{m+1}{j+1}/(m+1)$. Rearranging the factors then puts the expression in a form where the same identity, now with $n=m+1$ and $k=j+1$, replaces $\binom{m+1}{j+1}/(j+2)$ by $\binom{m+2}{j+2}/(m+2)$. Combining the two denominator factors gives the stated result.

**Key facts.** `FABL.cast_choose_div_succ`.
