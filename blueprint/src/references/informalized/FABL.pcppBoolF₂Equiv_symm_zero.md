<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.pcppBoolF₂Equiv_symm_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Image of Zero

**Claim.** The inverse image of $0$ under the equivalence between Booleans and $\mathbb F_2$ is `false`.

**Proof.** Apply injectivity of the equivalence to reduce the claim to showing that the image of `false` is $0$. By the defining computation of the equivalence, that image is $0$, so the inverse image must be `false`.
