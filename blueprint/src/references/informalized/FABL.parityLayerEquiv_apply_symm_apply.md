<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityLayerEquiv_apply_symm_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Inverse for Layer Indexing

**Claim.** For natural numbers $r$ and $q$, applying the layer equivalence after its inverse returns the original pair of a position and a parity block assignment.

**Proof.** An equivalence is a bijection, so composing its inverse with the equivalence in this order fixes every element of its target. Applying this defining inverse identity to the pair $i$ gives the claim.
