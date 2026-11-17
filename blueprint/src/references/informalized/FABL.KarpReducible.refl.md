<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.KarpReducible.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of Karp Reducibility

**Claim.** Every Boolean language is Karp reducible to itself.

**Proof.** Use the identity map on Boolean strings. It is polynomial-time computable, and an input belongs to the language exactly when its identical image does. Thus the identity map witnesses the reduction.
