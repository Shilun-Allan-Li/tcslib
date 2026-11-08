<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaSeedLength.lean :: FABL.card_violaSmallBiasSamplerSeedSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Sampler Seed Space

**Claim.** For nonzero $ell$, the set of $d$-tuples of pairs of elements of the degree-$ell$ extension field of the two-element field has cardinality $2^{2dell}$.

**Proof.** The extension field has cardinality $2^\ell$ (`binaryExtensionField_natCard`). A pair of its elements therefore has cardinality $(2^\ell)^2$, and a function from a $d$-element set into this pair space has cardinality $((2^\ell)^2)^d$. The exponent laws give $2^{2d\ell}$, as claimed.

**Key facts.** `FABL.binaryExtensionField_natCard`.
