<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.binaryLabeledSample_target -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary encoding of a labeled sample

**Claim.** Encoding the labeled sample $(x,f(x))$ gives the binary encoding of $x$ together with the binary encoding of $f(x)$ evaluated at that encoded input.

**Proof.** The encoded sample is a pair. Its first component is the binary encoding of $x$ by definition, so the first components agree. For the second component, the definition encodes the label $f(x)$ by the inverse sign equivalence. The definition of the binary encoding of the target, evaluated at the encoded input, applies that same inverse equivalence to $f$ at the corresponding sign-cube point. The equivalence laws identify that point with $x$, so the second components agree as well.
