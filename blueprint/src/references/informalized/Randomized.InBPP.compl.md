<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.InBPP.compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure for Bounded Error

**Claim.** If the verifier model is closed under negating verifier answers and $L$ belongs to its bounded-error class, then the complement of $L$ belongs to that class as well.

**Proof.** Choose a verifier $M$ and polynomial randomness bound witnessing that $L$ is in the class. Use the negated verifier, which remains efficient by the assumed closure under negation. On an input in the complement of $L$, the original verifier rejects with probability at least $2/3$, so its negation accepts with at least that probability. On an input in $L$, the original verifier accepts with probability at least $2/3$, so its negation rejects with at least that probability. These are exactly the two required guarantees for the complement; the equalities of probabilities follow because negating a Boolean answer exchanges true and false (`randProb_congr`).

**Key facts.** `Randomized.randProb_congr`.
