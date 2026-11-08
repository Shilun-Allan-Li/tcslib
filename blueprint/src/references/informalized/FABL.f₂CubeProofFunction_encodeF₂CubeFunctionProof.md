<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.f₂CubeProofFunction_encodeF₂CubeFunctionProof -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding and Decoding Boolean Functions

**Claim.** Encoding a function from the binary cube to the sign set as a Boolean function on the finite index set of size $2^n$, then decoding it, recovers the original function at every input.

**Proof.** Fix an input $x$. The encoding places at the index corresponding to $x$ the Boolean value obtained by converting the original sign value back through the Boolean-to-sign equivalence. Decoding reads the table at the index corresponding to $x$ and converts that Boolean value to a sign. The index equivalence and its inverse cancel, and the two conversions cancel because they are inverse equivalences. Hence the decoded value at $x$ is the original function value. Since this holds for every $x$, the functions agree.
