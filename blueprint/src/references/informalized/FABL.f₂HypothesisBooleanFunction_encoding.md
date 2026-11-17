<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.f₂HypothesisBooleanFunction_encoding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding and decoding Boolean functions

**Claim.** Encoding a sign-valued Boolean function as a binary-valued function and then decoding it recovers the original function at every input.

**Proof.** Evaluate the decoded function at an arbitrary sign-cube input $x$. By definition, decoding first converts $x$ to its binary-cube counterpart, applies the binary encoding of $g$, and converts the resulting bit back to a sign. The encoding applies the inverse conversion to that same binary-cube input and then evaluates $g$. The two cube conversions cancel, as do the conversions on the output, leaving $g(x)$. Since this holds at every input, the functions are equal.
