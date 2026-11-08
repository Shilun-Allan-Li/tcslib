<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.linearForm_neg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Reversal of a Linear Form

**Claim.** Negating every coordinate of a Boolean-cube vector negates the value of any linear form on that vector.

**Proof.** At each coordinate, the sign value of the negated input is the negative of the original sign value: the coordinate is either $1$ or $-1$. Multiplying by the fixed coefficient therefore negates each summand in the defining sum. The sum of these negated terms is the negative of the original sum.
