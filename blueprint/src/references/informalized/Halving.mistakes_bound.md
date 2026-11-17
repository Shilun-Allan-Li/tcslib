<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/Halving.lean :: Halving.mistakes_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving Algorithm Mistake Bound

**Claim.** If the target belongs to the finite version space $V$, then on every finite input sequence the total number of mistakes is at most $\lfloor\log_2 |V|\rfloor$.

**Proof.** Proceed by induction on the input sequence, with the version space allowed to vary in the induction hypothesis. For the empty sequence there are no mistakes. For a sequence beginning with $x$, let $y$ be the target's label on $x$ and let $V'$ be the version space after retaining hypotheses that predict $y$. The target remains in $V'$ (`Halving.target_mem_update`), so the induction hypothesis bounds the remaining mistakes by $\lfloor\log_2|V'|\rfloor$. If the prediction on $x$ is correct, there is no first-step mistake; moreover $V'\subseteq V$ (`Halving.update_subset`), so monotonicity of the integer logarithm gives $\lfloor\log_2|V'|\rfloor\le\lfloor\log_2|V|\rfloor$. If the prediction is wrong, the version space is halved (`Halving.mistake_halves`), and it is nonempty because it contains the target. The logarithm increment under doubling (`Halving.log_succ_le_log_of_double_le`) therefore gives $\lfloor\log_2|V'|\rfloor+1\le\lfloor\log_2|V|\rfloor$. Adding the one mistake on $x$ to the induction bound for the remainder proves the result.

**Key facts.** `Halving.target_mem_update`, `Halving.update_subset`, `Halving.mistake_halves`, `Halving.log_succ_le_log_of_double_le`.
