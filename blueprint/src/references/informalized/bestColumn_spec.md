<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ZeroSumGame.lean :: bestColumn_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimality of the Best Column

**Claim.** The selected column $j^*$ minimizes the row player’s expected payoff: $v(j^*)\le v(j)$ for every column $j$.

**Proof.** The finite set of column actions is nonempty, so the minimum existence result for a function on a finite nonempty type supplies a column attaining the minimum of $j\mapsto v(j)$. The definition of $j^*$ chooses such a column, and the defining property of that minimum gives $v(j^*)\le v(j)$ for each $j$.
