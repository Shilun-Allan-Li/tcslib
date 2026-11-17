<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: log_potential_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step logarithmic potential bound

**Claim.** For a valid loss sequence and positive learning rate, the change in log potential at round $t$ is at most $-(1-e^{-\eta})$ times the learner's expected loss at that round.

**Proof.** The potentials at times $t$ and $t+1$ are positive, so their logarithms are defined and their difference is the logarithm of their ratio. The one-step potential ratio bound (`potential_ratio_le`) says this ratio is at most $1-(1-e^{-\eta})\widehat{\ell}_t$. The ratio is positive, and the right-hand side is positive as well. By monotonicity of the logarithm, the log of the ratio is at most the log of that upper bound. Applying $\ln x\le x-1$ to the upper bound gives a result of $-(1-e^{-\eta})\widehat{\ell}_t$, as required.

**Key facts.** `potential_pos`, `potential_ratio_le`.
