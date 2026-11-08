<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.shiftedBinomialProbability_succ_same -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted binomial probability recurrence

**Claim.** For natural numbers $m,c,j$ with $j\le c$, the shifted binomial probability at $(m,c+1,j)$ equals its value at $(m,c,j)$ multiplied by $(2m+c+1)/(2(m+c+1-j))$.

**Proof.** Increasing $c$ to $c+1$ raises the upper binomial index by one while keeping the lower index $m+j$ fixed; the denominator power of $2$ acquires one additional factor of $2$. The binomial coefficient recurrence gives $\binom{2m+c+1}{m+j}(m+c+1-j)=(2m+c+1)\binom{2m+c}{m+j}$. Here $j\le c$ ensures the displayed denominator is positive. Substitution into the probability ratio, including the extra factor of $2$, proves the formula.
