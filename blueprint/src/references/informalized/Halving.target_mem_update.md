<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/Halving.lean :: Halving.target_mem_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target Survives Its Update

**Claim.** If the target belongs to $V$, then it remains in the updated version space when the update uses the label assigned by the target itself.

**Proof.** The update retains exactly those members of $V$ whose prediction on $x$ equals the supplied label. The target is already in $V$, and its prediction equals the label $\mathrm{eval}(\mathrm{target},x)$ used for this update. Hence it is retained.
