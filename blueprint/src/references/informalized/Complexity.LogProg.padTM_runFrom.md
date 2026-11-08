<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean :: Complexity.LogProg.padTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Preserves Machine Runs

**Claim.** Padding a machine to $K$ work tapes commutes with running it for any number of steps, provided the original machine has at most $K$ work tapes.

**Proof.** The one-step padding identity (`padTM_step`) says that stepping the padded machine from a padded configuration gives the padding of the original one-step result. Iterating this commuting identity for $n$ steps gives the claimed equality of runs (`Turing.MultiTapeTM.runFrom_comm_of_step`).

**Key facts.** `Complexity.LogProg.padTM_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
