<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.signedDictator_neg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Dictator Under Global Negation

**Claim.** Negating every coordinate of $z\in\{-1,1\}^{n+1}$ negates the value of the signed dictator at coordinate $i$, whether or not the dictator is negated.

**Proof.** Consider the two possibilities for the negation flag. If the dictator is not negated, its value is the $i$th coordinate, which changes sign when the input is negated. If the dictator is negated, its value is the negative of that coordinate, and this too changes sign under input negation. Therefore in either case the signed dictator at $-z$ is the negative of its value at $z$.
