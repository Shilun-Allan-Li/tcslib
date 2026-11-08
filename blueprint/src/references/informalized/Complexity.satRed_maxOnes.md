<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_maxOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan of a unary run

**Claim.** Starting in state $4$ before a run of $v$ true bits, after exactly $v$ steps the machine is in state $4$ just after the run. Its counter head is at $j+v$, its counter length is $\max(n,j+v)$, and the second tape, its head, and the output are unchanged.

**Proof.** Induct on $v$. If $v=0$, the run is empty, so zero steps leave the configuration unchanged; the assumption $j\le n$ gives $\max(n,j)=n$.

For the induction step, separate the first true bit from the remaining $v$ bits. Reading this first bit in state $4$ advances the input and counter heads by one, keeps the machine in state $4$, and writes true at the current counter position. Since $j\le n$, the counter-write fact (\texttt{Complexity.satRedCounter\_write}) identifies the new length as $\max(n,j+1)$. Apply the induction hypothesis to the remaining run with this new length and head position; its head advances another $v$ places, and its counter length becomes $\max(\max(n,j+1),j+1+v)=\max(n,j+v+1)$. The second tape, its head, and the output are preserved at the first transition and through the induction hypothesis. The one-step configuration law (\texttt{Complexity.satRedAction\_apply}) and input-head advancement (\texttt{Turing.moveInputPos\_pos\_of\_ne\_right}) give the first transition, and the successor-run identity (\texttt{Turing.MultiTapeTM.runFrom\_succ\_eq\_step}) joins it to the remaining run.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.satRedCfg_input`, `Complexity.satRedAction_apply`, `Complexity.satRedCounter_write`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
