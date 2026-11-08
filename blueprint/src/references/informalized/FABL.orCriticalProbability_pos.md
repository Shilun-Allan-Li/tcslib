<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.orCriticalProbability_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the critical probability

**Claim.** For every natural number $n>0$, the critical probability $1-\exp(-\log(2)/n)$ is positive.

**Proof.** Since $2>1$, its logarithm is positive. The real number represented by $n$ is also positive, so $-\log(2)/n<0$. The exponential is strictly increasing and sends $0$ to $1$, giving $\exp(-\log(2)/n)<1$. Subtracting this inequality from $1$ proves the claim.
