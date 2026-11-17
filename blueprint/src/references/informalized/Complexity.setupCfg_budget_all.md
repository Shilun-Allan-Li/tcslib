<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_budget_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Budget Rounds

**Claim.** If the little-endian value of the bit word is $v$, then after $(v+1)(2|w|+(a+1)+4)$ steps the schedule is in unary-start phase, with the stated heads and tapes and with a budget word of the same length.

**Proof.** Induct on $v$. If $v=0$, the borrow pass underflows: `budgetBorrow_underflow` says its final carry is true, and `setupCfg_budget_round` then gives the required unary-start configuration in one round. Its output word has the same length by `budgetBorrow_length`; the zero-value arithmetic makes the unary count and head agree with the claimed formula. For the successor case, the value of $w$ is positive. Thus `budgetBorrow_value` shows that one borrow pass reduces its value by one, while `budgetBorrow_underflow` shows that this pass ends without a carry. Apply `setupCfg_budget_round`: it advances the unary count by $a+1$, leaves the budget head at the word-length position, and returns to budget-start with the reduced word. Apply the induction hypothesis to that word and the increased unary count. The round lengths add by `runFrom_add`; `budgetBorrow_length` preserves the word length, and the resulting count simplifies to $N+(a+1)(v+1)$. The induction hypothesis supplies a final word of that same length and the claimed unary-start configuration.

**Key facts.** `Complexity.budgetBorrow_underflow`, `Complexity.setupCfg_budget_round`, `Complexity.budgetBorrow_length`, `Complexity.budgetBorrow_value`, `Turing.MultiTapeTM.runFrom_add`.
