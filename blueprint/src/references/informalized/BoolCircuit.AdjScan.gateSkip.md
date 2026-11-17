<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.gateSkip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Gate Scan Step

**Claim.** Under the stated oracle and encoding hypotheses, the scan can move from the gate-reading configuration with registers $(p,c,a)$ to the next gate-reading configuration with registers $(p+1+|\mathrm{encode}(g)|,c+1,a')$ for some $a'\le B$, while all registers remain bounded by $B$ before arrival.

**Proof.** The encoded gate begins with a marker bit. Since the suffix of $E$ at position $p$ is nonempty, the length bound for a nonempty prefix (`le_of_drop`) gives $p+1+|\mathrm{encode}(g)|\le |E|\le B$. The gate encoding has two kind bits, so dropping the marker and those two bits leaves precisely the encoded argument list followed by the remainder (`drop_add_of_drop`). Also, the gate encoding length is two plus the argument-list encoding length (`length_gate_encode`).

From the gate-reading state, the scan increments the gate counter and advances the position three places, reaching the argument-reading state with the appropriate updated registers. The register bound at each of these intermediate configurations follows from the triple-register bound (`gd_rg`) and the assumed bounds on $c$ and $a$, together with the prefix-length bound on $p$. Apply the argument-list scan result (`argsSkip`) to the remaining suffix: it advances past the encoded arguments, returns a register value $a'\le B$, and reaches the next gate-reading state. The position and counter there are exactly $p+1+|\mathrm{encode}(g)|$ and $c+1$, respectively. Chaining these transitions gives the required reachability and bounds all configurations strictly before arrival.

**Key facts.** `BoolCircuit.AdjScan.le_of_drop`, `BoolCircuit.AdjScan.drop_add_of_drop`, `BoolCircuit.AdjScan.length_gate_encode`, `BoolCircuit.AdjScan.argsSkip`, `BoolCircuit.AdjScan.gd_rg`, `Complexity.LogProg.AReach.step`.
