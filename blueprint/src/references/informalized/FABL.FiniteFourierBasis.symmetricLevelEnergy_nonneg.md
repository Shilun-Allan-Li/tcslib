<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.symmetricLevelEnergy_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Symmetric Level Energy

**Claim.** For every function and every level, the symmetric level energy is nonnegative.

**Proof.** By definition, the symmetric level energy is zero when the level is zero, which is nonnegative. At every other level it is the energy of an orthogonal component, and that energy is nonnegative (`orthogonalComponentEnergy_nonneg`).

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponentEnergy_nonneg`.
