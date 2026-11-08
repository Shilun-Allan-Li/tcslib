<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.orCriticalProbability_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical probability bounds

**Claim.** For every natural number $n$, the critical probability $1-\exp(-\log(2)/n)$ lies in $[0,1]$.

**Proof.** Split into $n=0$ and $n\ne0$. When $n=0$, the defining expression simplifies to $1$, which belongs to the interval. Otherwise $n>0$, so the positivity theorem for the critical probability gives the lower bound $0\leq 1-\exp(-\log(2)/n)$ (\texttt{FABL.orCriticalProbability\_pos}). For the upper bound, the exponential is positive, hence $1-\exp(-\log(2)/n)\leq1$.

**Key facts.** `FABL.orCriticalProbability_pos`.
