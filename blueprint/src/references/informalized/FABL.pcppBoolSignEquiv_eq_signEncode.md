<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.pcppBoolSignEquiv_eq_signEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of Booleans

**Claim.** For every Boolean $b$, its image under the Boolean-to-sign equivalence is $(-1)^c$, where $c$ is its image under the Boolean-to-field equivalence.

**Proof.** The Boolean-to-sign equivalence is defined as the composite of the Boolean-to-$\mathbb F_2$ equivalence and the sign equivalence whose map sends $c$ to $(-1)^c$. Thus its value at $b$ is exactly $(-1)^{\mathrm{image}(b)}$.
