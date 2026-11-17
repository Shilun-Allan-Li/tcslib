<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasOutputBit.lean :: FABL.executableBinaryDotProductState_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive dot product state

**Claim.** After $k$ steps, the recursive binary dot product state equals the sum of the coordinate products over indices below $k$, with out-of-range coordinates interpreted as zero.

**Proof.** Proceed by induction on $k$. At $k=0$, the state is zero and the sum over the empty range is zero. For the successor step, the recursion adds the product of the two coefficients at index $k$ to the state after $k$ steps. By the induction hypothesis, that earlier state is the sum over indices below $k$; adjoining the new term gives exactly the sum over indices below $k+1$.
