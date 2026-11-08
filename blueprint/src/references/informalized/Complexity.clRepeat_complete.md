<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeat_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Repetition of Clean Calls

**Claim.** If each of the first $N$ iterates can be produced by a clean call of at most $B$ steps, then the repetition controller reaches its completed state with word $f^{[N]}(s)$ and clock cursor $N$ in at most $N(B+2)+1$ steps.

**Proof.** Induct on the number $j\le N$ of completed calls. For $j=0$, the controller is already in its start phase with word $s=f^{[0]}(s)$ and cursor zero. For the induction step, suppose the controller reaches that phase with word $f^{[j]}(s)$ and cursor $j$ after $a\le j(B+2)$ steps. The clean-call hypothesis supplies a call of duration $b\le B$, positive, that transforms this word to $f^{[j+1]}(s)$ without entering the exit state earlier. The one-round simulation lemma advances the controller from cursor $j$ through that call and its two bookkeeping steps to the start phase with the updated word and cursor $j+1$ (`Complexity.clRepeat_round`). Combining the previous run and this round uses the addition law for run times (`Turing.MultiTapeTM.runFrom_add`), giving total time at most $(j+1)(B+2)$. At $j=N$, one final controller step detects that the unary clock is exhausted and enters the completed state. The unary buffer has no symbol at cursor $N$ (`Turing.FinTM.bufferTape_nat` and the fact that the replicate word has length $N$); the controller therefore takes its terminal control action, which leaves the tapes and output unchanged (`Turing.FinTM.controlAction_apply`), and its zero input movement fixes the input head (`Turing.moveInputPos_zero`). This adds one step, giving the bound $N(B+2)+1$. The iterate index updates from $f^{[j]}(s)$ to $f^{[j+1]}(s)$ at each round by the definition of function iteration.

**Key facts.** `Complexity.clRepeat_round`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
