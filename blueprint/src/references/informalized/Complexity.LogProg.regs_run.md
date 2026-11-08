<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.regs_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Heads Return After a Call

**Claim.** Under the stated call, buffer, register-box, side-predicate, and no-repeated-arguments hypotheses, the compiled machine returns from the specified successor configuration after finitely many steps. Throughout that run its register heads remain in the register box and its decider-head positions stay fixed; at the endpoint it is in the appropriate positive- or negative-answer program state with the specified tapes, positions, and output.

**Proof.** First, the no-repetitions hypothesis implies that the number of arguments is at most the number of registers. Also, every configuration formed by the return-position rule lies in the register box: registers outside the argument list keep their original positions, and the rule resets selected argument heads to zero, which remains between the box bounds $-1$ and the corresponding word length.

Proceed by induction on the number $k$ of arguments still to restore, with $a+k$ equal to the full argument-list length. If $k=0$, then $a$ is the full length, so the return successor is already the ordinary program state selected by the answer bit. Take time zero: the register-box assertion follows from the return-position observation, the decider positions are unchanged, and the endpoint configuration is the initial one with the required state and positions.

For the successor case, $a$ is a valid argument index and a valid register index. Let $rr$ be the register at position $a$. Since the list has no repetitions, this register's earlier return position has not been reset; its head is at the original in-box position. The side-predicate hypotheses ensure that if this head is at the left endpoint $-1$, it lies on the side where the return procedure can move right directly, and if it is at the right endpoint of its word, it lies on the side where the procedure scans back toward zero. Apply the register-return lemma (`Complexity.LogProg.retR_run`) to obtain a finite time $T_1$ at which this register has been restored to zero and the machine has advanced to argument position $a+1$. That lemma also controls the register heads throughout this first phase and keeps decider heads fixed.

Resetting $rr$ to zero at return position $a$ gives exactly the return-position assignment for $a+1$: all later arguments remain untouched, and the earlier arguments are already reset. Apply the induction hypothesis to the remaining $k$ arguments, obtaining a duration $T_2$ and the required bounds and endpoint from that intermediate configuration. The run-composition law (`Turing.MultiTapeTM.runFrom_add`) combines the phases into a run of length $T_1+T_2$. Before time $T_1$, use the first-phase bounds; from time $T_1$ onward, use the induction bounds. The first phase's box bounds are compatible with the next return-position box because only the current argument register moves, and the decider-head positions remain fixed in both phases. Composing the two endpoint equalities gives the stated final configuration.

**Key facts.** `Complexity.LogProg.retR_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_zero`.
