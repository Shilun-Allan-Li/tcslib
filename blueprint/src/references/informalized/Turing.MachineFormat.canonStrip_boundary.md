<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonStrip_boundary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary properties of trailing-one removal

**Claim.** For the word $v$ obtained by removing all trailing ones from $w$, its length is at most $|w|$, it is the prefix of $w$ of that length, all subsequent bits of $w$ are ones, and if the final position of $v$ exists then that bit of $w$ is zero.

**Proof.** Use the trailing-run decomposition (`canonStrip_split`): write $w=v++\mathrm{replicate}(r,true)$, where either $v$ is empty or $v=u++[false]$. The decomposition immediately gives $|v|\le |w|$ and that taking the first $|v|$ entries of $w$ returns $v$. Any index at or beyond $|v|$ but still within $w$ lies in the replicated suffix, so its bit is true. Finally, if $|v|=r_0+1$ for an index $r_0<|w|$, the last bit of $v$ exists and is false by the stated form of the prefix; hence $w[r_0]=false$.

**Key facts.** `Turing.MachineFormat.canonStrip_split`.
