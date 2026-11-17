<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/Halving.lean :: Halving.halving_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving Mistake Bound

**Claim.** For any finite initial version space containing the target, the Halving Algorithm makes at most $\lfloor\log_2 |H|\rfloor$ mistakes on every finite input sequence.

**Proof.** This follows directly from the general mistake bound for the Halving Algorithm (`Halving.mistakes_bound`): apply it to the evaluation map, target, initial version space $H$, and sequence $xs$. Its membership hypothesis is exactly the assumed fact that the target belongs to $H$.

**Key facts.** `Halving.mistakes_bound`.
