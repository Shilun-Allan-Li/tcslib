<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.extendProofWithFinalTrue_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a sequence with final value true

**Claim.** If a Boolean sequence on $m+1$ positions has value true at its last position, then restricting it to the first $m$ positions and appending true recovers the original sequence.

**Proof.** Compare the two sequences at each position. At the last position, the appended sequence has value true, which agrees with the assumed last value of the original sequence. At every earlier position, the appended sequence uses the original sequence's value at that same position. Thus the sequences agree everywhere.
