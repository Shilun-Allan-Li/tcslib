<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_increment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Complete Counter Increment

**Claim.** From the count state, the machine increments the stored word and advances the input head by one in $2\operatorname{carry}(b)+2$ steps, returning to the count state with the work head at zero.

**Proof.** First establish the carry-phase endpoint. The start transition moves from the count phase into the carry phase (the two possible initial transitions agree as required by $\texttt{counter_start}$); applying the carry result with empty prefix then reaches state $2$ with the incremented word and work head at $\operatorname{carry}(b)-1$. This takes $\operatorname{carry}(b)+1$ steps, by $\texttt{counter_carry}$. The run-splitting identities $\texttt{runFrom_succ_eq_step}$ and $\texttt{runFrom_add}$ organize these transitions. Now run the rewind phase for another $\operatorname{carry}(b)+1$ steps. The incremented word is long enough for this rewind, since its carry length is at most its length ($\texttt{counterInc_length}$). The rewind result returns the machine to state $0$ with work head at zero and leaves the tape unchanged ($\texttt{counter_rewind}$). Combining the two phase lengths gives $2\operatorname{carry}(b)+2$; the start transition also places the input head at $i+2$, as claimed.

**Key facts.** `Complexity.counter_start`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.counter_carry`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.counterInc_length`, `Complexity.counter_rewind`.
