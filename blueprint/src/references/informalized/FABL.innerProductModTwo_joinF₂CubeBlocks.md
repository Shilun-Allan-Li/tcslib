<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.innerProductModTwo_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign of a binary inner product

**Claim.** For every natural number $n$ and vectors $x,y\in(\mathbb{F}_2)^n$, the real sign encoding of their inner product modulo two equals the binary character evaluated at that inner product.

**Proof.** By the block identity for the inner product bit, evaluating that bit on the joined vector formed from $x$ and $y$ gives exactly $\langle x,y\rangle$ in $\mathbb{F}_2$ (`innerProductModTwoBit_joinF₂CubeBlocks`). Unfolding the real sign encoding therefore reduces the left side to the real value of the sign encoding of this same bit. The identity identifying that real value with the binary character (`signValue_signEncode_eq_binarySign`) gives the asserted equality.

**Key facts.** `FABL.innerProductModTwoBit_joinF₂CubeBlocks`, `FABL.signValue_signEncode_eq_binarySign`.
