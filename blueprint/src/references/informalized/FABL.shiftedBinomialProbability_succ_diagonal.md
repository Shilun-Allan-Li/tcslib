<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.shiftedBinomialProbability_succ_diagonal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal shifted binomial recurrence

**Claim.** For natural numbers $m,c$, the diagonal shifted binomial probability at $c+1$ equals its value at $c$ multiplied by $(2m+c+1)/(2(m+c+1))$.

**Proof.** Write each shifted probability as its binomial coefficient divided by the corresponding power of $2$. Increasing $c$ by one raises both the upper and lower indices of the diagonal coefficient by one, and doubles the denominator. The binomial coefficient recurrence gives $\binom{2m+c+1}{m+c+1}(m+c+1)=(2m+c+1)\binom{2m+c}{m+c}$. Dividing by the positive factors and accounting for the extra factor of $2$ in the denominator yields the stated ratio.
