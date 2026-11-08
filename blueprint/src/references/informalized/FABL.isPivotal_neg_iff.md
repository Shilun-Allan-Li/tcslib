<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.isPivotal_neg_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotality under negation

**Claim.** Negating every output of a function preserves whether it is pivotal at a given input and coordinate.

**Proof.** By definition, pivotality asks whether the two outputs at $x$ and its coordinate flip are unequal. Negating both outputs preserves inequality, because negation is injective. Therefore the negated function is pivotal exactly when the original function is pivotal.
