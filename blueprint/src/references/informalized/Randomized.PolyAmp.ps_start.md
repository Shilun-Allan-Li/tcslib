<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.ps_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Amplifier Semantics

**Claim.** Starting the amplifier at its initial label with all registers zero gives a terminating computation for every sequence of choice bits, keeps every register at most $B$, and has probability equal to the run value with parameters $K_*=2^{F\ell(|x|)}$, $K_*+1$, and $0$.

**Proof.** Write $n=|x|$, $\ell=\ell(n)$, and $K=2^{F\ell}$. The proof builds the initial computation in stages, maintaining the register bound. First, the input-length loop queries the input-length decider until it has stored $n$; the input-length query fact identifies each answer, and the loop reachability theorem supplies the bounded computation. It then copies the binary length into the scratch register and repeatedly halves that register while incrementing the $\ell$ register. Since the number of halvings is the bit length of $n$, this sets $\ell$ correctly. Two register-scaling loops set the space parameter to $cS\ell$ and the exponent to $F\ell$. The copy and shift loops then form $K=2^{F\ell}$ in its register. The hypotheses on configuration-code size and the displayed bound on $B$ ensure throughout that these intermediate values and scratch registers remain at most $B$. Finally, the copy loops initialize the number of runs and runs remaining to $K+1$, with the accepting count zero, and transfer control to the run loop. The run-loop theorem applies with the given space, code, and register bounds, yielding precisely the asserted run value. Each deterministic reachability segment preserves probabilistic semantics, so composing these segments proves the initial amplifier has the same semantics as that run-loop configuration.

**Key facts.** `Complexity.LogProg.inputLength_loop`, `Complexity.LogProg.AReach.mono`, `Complexity.LogProg.PSem.of_reach`, `Complexity.LogProg.PSem.inc`, `Complexity.Codec.halvCount_loop`, `Complexity.Codec.registerScale_loop`, `Complexity.LogProg.shl_run`, `Randomized.PolyAmp.Reg.le_v`, `Randomized.PolyAmp.ps_cp`, `Randomized.PolyAmp.ps_runs`.
