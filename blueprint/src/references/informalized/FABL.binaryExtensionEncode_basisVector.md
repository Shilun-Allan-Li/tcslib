<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.binaryExtensionEncode_basisVector -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Basis Vector

**Claim.** The field element corresponding to the $j$th coordinate basis vector is encoded as the vector that is $1$ at $j$ and $0$ elsewhere.

**Proof.** The basis vector in the field is defined as the inverse image of the coordinate vector supported at $j$ with value $1$. Applying the encoding to this inverse image returns the original coordinate vector, by the inverse-cancellation property of an equivalence.
