<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeat_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Clocked Repetition Round

**Claim.** Under the stated avoidance and exact-reachability hypotheses, one repetition round takes the controller from its test state with word $s$ and clock cursor $j$ to its test state with word $s'$ and cursor $j+1$ in exactly $t+2$ steps.

**Proof.** Because $j<N$, the clock tape contains `true` at cursor $j$ (`bufferTape_nat`). Thus the first controller step advances the cursor and enters the call state, without changing the simulated machine's tapes or word. The next $t$ steps simulate $C$ from entry: the call lemma (`Complexity.clRepeat_call`) shows that the run reaches the repetition controller's exit state with word $s'$ and cursor $j+1$, using the hypotheses that the simulated run avoids exit at all intermediate positive times and reaches exit at time $t$. One final controller step returns from that exit state to the test state. The run decomposition lemmas (`runFrom_succ_eq_step` and `runFrom_succ_eq_step'`) organize these steps as $1+t+1=t+2$; the return action leaves the input head, tapes, and output unchanged.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Complexity.clRepeat_call`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
