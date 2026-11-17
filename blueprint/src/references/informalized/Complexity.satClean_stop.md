<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satClean_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stopping wrapper contract

**Claim.** Under the stated bridge hypothesis, the wrapper that simulates the machine and silently halts upon reaching the designated exit state after at least one step satisfies the clean-module contract, with time bound increased from $B(n)$ to $B(n)+1$.

**Proof.** Fix an input and argument, and choose a bridge time $t$ supplied by the hypothesis. By the stopping-wrapper simulation property (Complexity.satStop_clean), after $t+1$ steps the wrapper is in the halting configuration with result $r(a)$ installed and output $s(a)$. This is a positive time and is at most $B(|a|)+1$. The wrapper has not halted earlier: the simulation does not halt before the bridge reaches its exit, and the hypothesis excludes that exit at every positive time before $t$. The first-halt principle for machine runs (Complexity.sat_call_first_halt) then provides a positive time $u\le t+1$ at which the wrapper first halts, with the same configuration as at time $t+1$. Therefore its first halting configuration has the required clean contents and output, and its time also obeys the bound $B(|a|)+1$. The wrapper retains the positive number of work tapes of the original machine.

**Key facts.** `Complexity.satStop_clean`, `Complexity.sat_call_first_halt`.
