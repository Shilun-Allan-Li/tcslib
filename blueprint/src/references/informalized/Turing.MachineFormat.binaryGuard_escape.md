<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.binaryGuard_escape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Escape of the Binary Guard Machine

**Claim.** If the input is too short to accommodate the counter’s prescribed advance, the binary guard machine reaches escape within the stated time bound, preserves the output, and has input position $|x|+1$; before that time it is neither done nor escape.

**Proof.** Let $r_0=\lfloor(|x|-j)/(b+1)\rfloor$. Division with remainder shows that after $r_0$ complete guard blocks the machine is at position $j+(b+1)r_0$, with fewer than $b+1$ input symbols remaining. The input-too-short hypothesis implies $r_0< N$, where $N$ is the value represented by $w$; otherwise $j+(b+1)N\le |x|$. For every $r\le r_0$, the guard-block orbit formula gives position $j+(b+1)r$, which is within the input.

The final partial block, by `guardBlock_short`, reaches the end of the input and enters the guard’s terminal state after the $r_0$-th full block. Each full block starts in its initial phase, takes positive time, and avoids both that initial phase and the terminal state at all intermediate times (`guardBlock_segment`). Thus the hypotheses of `counterLoopTM_run_escape` hold: the counter has at least $r_0+1$ rounds available, all required rounds follow the guard-block behavior, and the next orbit is the terminal guard configuration. The counter loop consequently reaches escape, with the output still $out$ and input position $|x|+1$, while neither done nor escape occurs earlier.

For the bound, each of the $r_0+1$ blocks takes at most $b+1$ steps, and `counterOverhead_le_of_le` bounds the counter overhead by $4(r_0+1)+2|w|$. Hence the total is at most $(b+5)(r_0+1)+2|w|$. Since $r_0+1\le |x|+1$, this is at most $(b+5)(|x|+1)+2|w|$.

**Key facts.** `Turing.MachineFormat.guardBlock_orbit`, `Turing.MachineFormat.guardBlock_short`, `Turing.MachineFormat.guardBlock_segment`, `Turing.counterLoopTM_run_escape`, `Turing.counterOverhead_le_of_le`.
