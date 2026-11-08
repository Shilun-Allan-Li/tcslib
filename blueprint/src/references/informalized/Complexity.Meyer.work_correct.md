<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.work_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Work Tape Encoding

**Claim.** Under the stated goodness, correctness, and range hypotheses, the encoded symbol on work tape $h$ at time $t+1$ and offset $d$ equals the symbol actually present there after $t+1$ steps.

**Proof.** The one-step correctness rule for the work-tape encoding identifies the encoded symbol at time $t+1$ with the machine’s work-tape update rule applied to the time-$t$ configuration and its read symbols ( `Complexity.Meyer.work_rule`). The run of length $t+1$ is the one-step successor of the run of length $t$ ( `Turing.MultiTapeTM.runFrom_succ_eq_step'`), and the work-tape update rule for that successor agrees with the actual read/write transition ( `Complexity.Meyer.RW_step`). It remains to replace the encoded tape contents supplied to the update rule by the actual tape contents. The update at offset $d$ depends only on positions $e$ with $|e|\le |d|+1$ ( `Complexity.Meyer.ruleW_congr`). For each such $e$, the assumed correctness at time $t$ applies: the bound on $d$ implies $|e|+t\le2^W-1$, so the encoded value equals the actual value there. Substituting these equal local tape values into the update rule yields the actual symbol at time $t+1$, as required.

**Key facts.** `Complexity.Meyer.work_rule`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.RW_step`, `Complexity.Meyer.ruleW_congr`.
