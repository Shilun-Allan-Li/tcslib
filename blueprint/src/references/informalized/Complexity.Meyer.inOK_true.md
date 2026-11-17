<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.inOK_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input consistency on a genuine run

**Claim.** Under the answer-table correctness and range hypotheses, the input consistency predicate returns true on the machine's state and scanned symbols at time $t$, for every permitted integer position $e$.

**Proof.** First, the signed integer $e$ is encoded by its sign and magnitude so that the two address conventions used by the predicate represent positions $e$ and $e+1$. The identities `edge_c1` and `edge_c2` establish these conversions. For each of the two queried times, the encoded answer table returns the actual input symbol at the corresponding signed position: this is the content of `sv_true_none`. The hypotheses ensure that the queried times and addresses lie within the table's range. Thus the predicate's two candidate symbol values at time $t$ and the corresponding values at time $t+1$ can be read as actual input symbols of the machine configurations.

The proof then uses the fact that the next run configuration is one machine step after the current one (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) and that the input-symbol function evolves according to the machine's input-head movement (`RI_step`). If the current configuration is halted, or the transition keeps the head still, the two positions retain their symbols. For a right move, either the move is clamped at a blank boundary, in which case the same-position comparisons hold, or the symbol at position $e$ after the move is the old symbol at $e+1$. For a left move the analogous alternatives give either the same-position comparisons or the old symbol at $e$ appearing at position $e+1$. In each case the encoded predicate's comparisons are precisely these equalities, so it evaluates to true.

**Key facts.** `Complexity.Meyer.edge_c1`, `Complexity.Meyer.edge_c2`, `Complexity.Meyer.sv_true_none`, `Complexity.Meyer.symvA_NumVal`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.RI_step`.
