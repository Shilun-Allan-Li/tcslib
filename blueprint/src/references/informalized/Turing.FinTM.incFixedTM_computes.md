<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.incFixedTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Increment Runtime

**Claim.** For every Boolean word $x$, the fixed-width increment machine halts after exactly $3(|x|+1)$ steps and outputs its fixed-width increment, using the empty word when the increment overflows.

**Proof.** Use the two structural cases for fixed-width increment (`incFixed_cases`). If every bit is true, the increment is undefined, so the specified output is empty. The machine scans the whole word without emitting, then halts; the scan computation gives this behavior in $|x|+1$ steps. The computation characterization (`computesInTime_iff`) turns these state and output facts into a time-and-space computation, and monotonicity in the time bound (`ComputesInTime.mono`) extends it to the claimed time. If instead $x$ consists of $j$ true bits, then a false bit, then a suffix, the increment changes the first $j$ bits to false and that next bit to true. The machine first scans the $j$ true bits, reaching the false bit after $j+1$ steps (`scanTrues_run`); reading that false bit enters the rewind state. Rewinding takes another $j+1$ steps (`rewind_scan`), returning the head to the start. The emission scan writes false for the first $j$ positions and then true at the changed bit (`scanTrues_run`), after which the copy phase emits the unchanged suffix and halts (`scanCopy_suffix`). Concatenating these run segments (`runFrom_add`) yields output $\underbrace{00\cdots0}_{j}\,1$ followed by the suffix. Their total time is $(j+1)+(j+1)+(j+1)+(|\text{suffix}|+1)=3(j+1)+|\text{suffix}|+1=3(|x|+1)$, since $|x|=j+1+|\text{suffix}|$. The computation characterization supplies the claimed computation at this exact time.

**Key facts.** `Turing.FinTM.incFixed_cases`, `Turing.FinTM.scanTrues_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.rewind_scan`, `Turing.FinTM.scanCopy_suffix`.
