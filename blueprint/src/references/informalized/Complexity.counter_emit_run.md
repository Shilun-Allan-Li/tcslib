<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_emit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Emission

**Claim.** After $i\le|b|$ steps in the emit phase, the work head is at $i$, the tape remains $b$, and the output is the length-$i$ prefix of $b$, while the state and input-head position remain unchanged.

**Proof.** Induct on $i$. At zero steps the initial configuration has the asserted values. For the successor step, the induction hypothesis places the work head at $i$ while $i<|b|$. Thus the symbol read there is the $i$th bit of $b$. The emit transition leaves the tape unchanged, keeps the machine in the emit state, and advances the work head one cell; it also appends that bit to the output. The appended bit turns the length-$i$ prefix into the length-$(i+1)$ prefix. The input-head movement is zero, so its position is preserved ($\texttt{moveInputPos_zero}$); the run decomposition into the previous run and one further step is $\texttt{runFrom_succ_eq_step'}$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
