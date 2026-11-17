<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step equals one-step iteration

**Claim.** For every Boolean input word and configuration of the transducer on it, running the machine for one step gives the same configuration as applying its one-step transition.

**Proof.** A run of length one is, by the successor-run identity, the run obtained by first taking one step and then running for zero steps. A zero-length run leaves its configuration unchanged, so this is exactly the one-step transition.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
