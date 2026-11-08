<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.collision_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision of the Uniform Distribution

**Claim.** For a nonempty finite set, the collision probability of its uniform distribution is the reciprocal of its cardinality.

**Proof.** Every outcome under the uniform distribution has probability $1/|[$. In the collision sum, each of the $|[$ terms is therefore $(1/|[|)^2$. Summing gives $|[|/|[|^2=1/|[|$; the nonemptiness assumption ensures the cardinality is nonzero.

**Key facts.** `TCSlib.InformationTheory.FinDist.uniform_apply`.
