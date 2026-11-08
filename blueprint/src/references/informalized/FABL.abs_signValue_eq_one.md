<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_signValue_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Value of a Sign

**Claim.** For every sign $s\in\{-1,1\}$, its real value has absolute value $1$.

**Proof.** Every unit in $\mathbb Z$ is either $1$ or $-1$ (the two alternatives in `Int.units_eq_one_or`). If $s=1$, its real value is $1$, whose absolute value is $1$. If $s=-1$, its real value is $-1$, whose absolute value is also $1$.

**Key facts.** `Int.units_eq_one_or`.
