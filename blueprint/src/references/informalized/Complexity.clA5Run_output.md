<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Run_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output as a Concatenation of Emissions

**Claim.** After $T$ steps, the machine's output is the chronological concatenation of the optional bits emitted by the snapshots at times $0,1,\ldots,T-1$.

**Proof.** Induct on $T$. At zero steps, both sides are empty. For the successor case, the output after $T+1$ steps is the output after $T$ steps followed by the optional symbol emitted by the next transition (`Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`). By induction, the earlier output is the concatenation of emissions at times $0$ through $T-1$. The range of times through $T$ is the previous range with the single final time $T$ appended, so its flat-map concatenation adds precisely the emission of the snapshot at time $T$. If the machine is halted at that snapshot, it emits nothing; otherwise the transition's output is exactly the snapshot's defined emission. Thus the two expressions agree.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
