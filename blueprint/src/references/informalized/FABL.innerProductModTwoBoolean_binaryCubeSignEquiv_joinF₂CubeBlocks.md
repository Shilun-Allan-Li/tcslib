<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of the Binary Inner Product

**Claim.** For any natural number $n$ and vectors $x,y\in\mathbb{F}_2^n$, evaluating the Boolean function on the sign encoding of their concatenation gives the sign encoding of their inner product modulo two.

**Proof.** Unfold the Boolean function. The inverse sign encoding sends each sign coordinate back to its binary coordinate, so applying it to the sign encoding of the concatenated blocks recovers those blocks. The block decomposition therefore returns $x$ and $y$, and the inner product bit is $x\cdot y$. Encoding that bit as a sign gives the stated equality.
