<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.SparseFourierHypothesis.natOfBits_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from binary bits

**Claim.** For every natural number $k$, interpreting the bits in its binary bit list as a natural number returns $k$.

**Proof.** Use binary recursion on $k$. At zero, its bit list is empty, and the interpretation of the empty list is zero. In the recursive case, write $k$ in canonical binary form as the number represented by the bits of a smaller number with one final bit appended. The binary bit-list identity (`Nat.bits_append_bit`) gives this form explicitly. Interpreting that list applies the final bit operation to the interpretation of the smaller number; the induction hypothesis identifies that number with the smaller number in the recursive case, yielding $k$.
