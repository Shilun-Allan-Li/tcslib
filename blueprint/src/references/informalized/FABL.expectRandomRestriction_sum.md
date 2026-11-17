<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expectRandomRestriction_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of restriction expectation

**Claim.** The expected random restriction of a finite pointwise sum is the sum of the expected random restrictions of its terms.

**Proof.** Induct on the finite index set. For the empty set, the pointwise sum is zero, and its expectation is zero by the constant-function identity (`expectRandomRestriction_const`). For a set formed by adjoining a new index to a smaller set, separate that index's summand from the sum over the smaller set. Linearity for two functions (`expectRandomRestriction_add`) splits the expectation accordingly, and the induction hypothesis identifies the remaining term with the sum of the corresponding expectations. The finite-sum decomposition completes the induction.

**Key facts.** `FABL.expectRandomRestriction_const`, `FABL.expectRandomRestriction_add`.
