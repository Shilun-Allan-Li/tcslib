<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.expect_neg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Under Sign Reflection

**Claim.** For any real-valued function on the sign cube, its uniform average after replacing each sign vector by its negative equals its original uniform average.

**Proof.** Negation is a bijection of the sign cube, with itself as inverse. Reindexing the finite uniform average by this bijection leaves the average unchanged; hence the average of $u(-x)$ equals that of $u(x)$.
