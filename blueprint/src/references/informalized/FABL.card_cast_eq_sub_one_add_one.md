<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.card_cast_eq_sub_one_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Cardinality After Subtracting One

**Claim.** If a finite set has at least two elements, its cardinality viewed as a real number is one plus the real-valued cardinality obtained by subtracting one from its natural-number cardinality.

**Proof.** The hypothesis that the natural cardinality is at least two ensures it is at least one, so subtraction by one is valid under the natural-number cast formula: the real cast of a natural number minus one equals the real cast of the number minus the real cast of one. Rearranging gives the stated identity.
