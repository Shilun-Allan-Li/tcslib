<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.booleanFunctionF₂Encoding_resilientDegreeSharpnessFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding the Sharpness Function

**Claim.** The binary encoding of the sharpness function is the sum over $\mathbb F_2$ of the coordinate sum on the prefix and the monomial on its complement.

**Proof.** Expand the sharpness function as the parity on the prefix multiplied by the decoding of the monomial on the tail. The encoding rule for a parity multiplied by a Boolean function says its encoding is the coordinate sum on the parity set plus the encoding of the other factor. Apply this with the prefix and the decoded tail monomial. Encoding after decoding recovers the tail monomial, leaving exactly the stated sum.

**Key facts.** `FABL.booleanFunctionF₂Encoding_parityTimes`, `FABL.booleanFunctionF₂Encoding_booleanFunctionF₂Decoding`.
