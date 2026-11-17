<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.signValue_nandPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Sign Pair Value

**Claim.** For signs $a$ and $b$, the real value of their NAND sign pair is $\frac{-1-a-b+ab}{2}$.

**Proof.** Each sign, being a unit of the integers, is either $1$ or $-1$. In the four resulting cases, the NAND pair is $1$ only when both signs are $-1$, and is $-1$ otherwise. Substituting these values into the displayed expression gives $1$ in the first case and $-1$ in the other three, which are exactly the real values of the corresponding NAND outputs.
