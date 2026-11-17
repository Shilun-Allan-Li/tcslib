<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ZeroSumGame.lean :: bestRow_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimality of the Best Row

**Claim.** The selected row $i^*$ maximizes its expected payoff against the column player’s mixed strategy: $u(i)\le u(i^*)$ for every row $i$.

**Proof.** The finite set of row actions is nonempty, so the maximum existence result for a function on a finite nonempty type supplies a row attaining the maximum of $i\mapsto u(i)$. The definition of $i^*$ chooses such a row, and the defining property of that maximum gives $u(i)\le u(i^*)$ for every $i$.
