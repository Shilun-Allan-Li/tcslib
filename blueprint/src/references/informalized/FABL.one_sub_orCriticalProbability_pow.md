<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.one_sub_orCriticalProbability_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power at the OR critical probability

**Claim.** For a positive natural number $n$, if $p=1-\exp(-\log(2)/n)$, then $(1-p)^n=\tfrac12$.

**Proof.** By the definition of $p$, $1-p=\exp(-\log(2)/n)$. Raising to the $n$th power combines the exponent to give $\exp(n(-\log(2)/n))=\exp(-\log 2)$. Since $n>0$, division by $n$ is valid; and since $2>0$, $\exp(\log 2)=2$. Hence the expression is $1/2$.
