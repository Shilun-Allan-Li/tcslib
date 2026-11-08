<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.ps_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded walk computation

**Claim.** The program at $w0$ terminates within the register bound and accepts exactly when there is a walk from $s$ to $t$ of length at most $n-st$ in the graph encoded by the input.

**Proof.** Strengthen the result by induction on the permitted remaining walk length $d=n-st$. For $d=0$, the program accepts exactly when the current vertex equals the target, which is precisely the zero-length case of `WalkLe`. For a positive allowance, equality of source and target again gives an immediate accepting branch. Otherwise the program guesses a next vertex $j<n$ (`nsem_guess`). It checks the graph bit for the edge from $s$ to $j$: `pathOr_bit` identifies that bit with `pathEdge`, and `rowMajor_lt` ensures its position is within the encoded adjacency table. If the edge is absent, that guess rejects. If it is present, the program sets the current vertex to $j$, increases the step count by one, and invokes the induction hypothesis with one fewer allowed step. The register-copying principle `nsem_copy` implements the vertex update, and `ps_index` justifies the indexed graph-bit check under the input-length bound. Thus an accepting branch exists exactly when some $j<n$ is an outgoing neighbor of $s$ from which $t$ is reachable within the remaining allowance; this is the recursive positive-length clause of `WalkLe`. The equality and inequality branch rules, along with the increment, clear, oracle-call, and return rules, establish termination and boundedness throughout.

**Key facts.** `Complexity.LogProg.NSem.jeq_pos`, `Complexity.LogProg.NSem.ret`, `Complexity.LogProg.NSem.jeq_neg`, `Complexity.LogProg.NSem.clr`, `Complexity.LogProg.nsem_guess`, `Complexity.rowMajor_lt`, `Complexity.LogProg.ps_index`, `Complexity.LogProg.pathOr_bit`, `Complexity.LogProg.NSem.call_pos`, `Complexity.LogProg.NSem.call_neg`, `Complexity.LogProg.nsem_copy`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.NSem.congr`.
