<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseSmallBiasOutputList_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Bias Output List Length

**Claim.** The deterministic small-bias construction associated with an almost-wise input has an output list of length $2^{2d}$, where $d$ is the field degree of its associated small-bias input.

**Proof.** The cardinality result for the deterministic small-bias output multiset (`deterministicSmallBiasMultiset_card`) gives cardinality $(2^d)^2$. The list and multiset here enumerate the same outputs, so this cardinality is the output-list length. Rewriting $(2^d)^2$ as $2^{2d}$ gives the stated formula.

**Key facts.** `FABL.deterministicSmallBiasMultiset_card`.
