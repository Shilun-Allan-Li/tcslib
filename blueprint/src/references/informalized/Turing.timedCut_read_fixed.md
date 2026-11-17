<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_read_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Eight Fixed Action Bits

**Claim.** Under the stated table decomposition and register-agreement hypothesis, reading the remaining fixed action bits reaches successor decoding after exactly $n+1$ steps, with the register containing all eight bits and the cursor at $|l|+8$.

**Proof.** Induct on the number $n$ of remaining bits. When $n=0$, the condition $field+n=7$ forces the current field to be the eighth one. The table cursor therefore points to the corresponding bit in the serialized block: list indexing and the definition of the finite-indexed list show that the read is $bits(field)$. Updating the register at this last field yields the full function $bits$, since all earlier fields already agree by hypothesis. The interpreter's one-step transition then enters successor decoding. For the induction step, the current field is before the last one. The same list-index argument identifies the bit at the cursor. The transition reads it, advances the cursor by one, and updates the register. At the new field, the updated register agrees with $bits$ through all fields already passed: at the current index this follows from the update, and at earlier indices it follows from the induction hypothesis assumption. Apply the induction hypothesis to the next field and the remaining $n$ bits. The run identities (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`) identify the one-step transitions with runs, while `Turing.MultiTapeTM.runFrom_add` is not needed here: each induction step uses the successor-run equation directly. The buffer lookup on a natural cursor is the list lookup (`Turing.FinTM.bufferTape_nat`), and the one-step configuration change is given by `Turing.timedCut_Eval_step`.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.timedCut_Eval_step`.
