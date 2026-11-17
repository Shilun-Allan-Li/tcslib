<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.uniformProbability_eq_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Singleton

**Claim.** For a finite nonempty set $\Omega$ and $a\in\Omega$, the uniform probability of the event consisting only of $a$ is $1/|\Omega|$.

**Proof.** Uniform probability is the average of the event's indicator over $\Omega$. For the event $x=a$, that indicator is $1$ at exactly one element and $0$ elsewhere, so its sum is $1$. Dividing by the number of elements of $\Omega$ gives $1/|\Omega|$.
