<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.isBalanced_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balance under Boolean duality

**Claim.** If the real-valued form of a Boolean function has mean zero on the uniform sign cube, then the function obtained by negating its output at the coordinatewise negation of its input also has mean zero.

**Proof.** By the mean transformation formula, the mean of the dual function is the negative of the mean of the original function (`mean_booleanDual`). The original mean is zero by hypothesis, so its negative is zero as well.

**Key facts.** `FABL.mean_booleanDual`.
