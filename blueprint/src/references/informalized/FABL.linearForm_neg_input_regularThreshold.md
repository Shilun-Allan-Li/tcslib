<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.linearForm_neg_input_regularThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Reversal of a Linear Form

**Claim.** Negating every coordinate of a Boolean-cube vector negates the value of any linear form on that vector.

**Proof.** For each coordinate, the sign value after negation is the negative of its original sign value, since each coordinate is either $1$ or $-1$. Thus every coefficient-weighted summand changes sign, and so does their sum.
