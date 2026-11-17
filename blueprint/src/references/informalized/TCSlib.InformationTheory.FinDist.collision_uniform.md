<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.collision_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision of the Uniform Distribution

**Claim.** For a nonempty finite set, the collision probability of its uniform distribution is the reciprocal of its cardinality.

**Proof.** Let $N$ be the cardinality of the finite type. Uniformity gives every outcome probability $1/N$, so the collision sum over the $N$ outcomes is $N(1/N)^2=1/N$. The nonemptiness assumption ensures $N>0.

**Key facts.** `TCSlib.InformationTheory.FinDist.uniform_apply`.
