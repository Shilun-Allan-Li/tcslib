<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.output_runFrom_eq_flatMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output as a Concatenation of Emissions

**Claim.** The output after $t$ steps is the ordered concatenation of the optional symbols emitted by the transitions prescribed at times $0,\ldots,t-1$, with halted snapshots contributing no symbol.

**Proof.** Proceed by induction on $t$. At time zero the output is empty, as is the concatenation over an empty range. For the induction step, the run after $t+1$ steps is obtained by taking one step from the configuration at time $t$ (`runFrom_succ_eq_step'`). A step appends to the current output the optional symbol prescribed by the current configuration (`step_output`). By the induction hypothesis, the current output is already the concatenation of emissions from times $0$ through $t-1$. The range of times through $t$ consists of those earlier times followed by the single time $t$, so its concatenation appends exactly the emission at that snapshot. If the snapshot is halted, its emission is empty; otherwise it is the output component of the transition prescribed there. This identifies the added symbol in either case and completes the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
