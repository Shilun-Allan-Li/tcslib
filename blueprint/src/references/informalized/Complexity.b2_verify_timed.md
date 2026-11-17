<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_verify_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Verifier Completion

**Claim.** If the verifier halts within time $T$ with output $[b]$, then every choice word of length $T+1$ makes the host halt with output $[b]$ from the verifier-phase initialization.

**Proof.** Choose the least time $t$ at which the verifier run from its initial configuration is halted. The assumed time-$T$ computation ensures $t\le T$ and that the verifier is halted at $t$. By the computation characterization (`Turing.FinTM.computesInTime_iff`), its output at time $t$ is an output of the verifier on $y$; uniqueness of outputs (`Turing.FinTM.ComputesInTime.output_unique`) therefore identifies it with $[b]$. Run the host on the first $t$ choices. Every earlier verifier configuration is live by minimality of $t$, so the relocated-run result (`Complexity.b2_verify_run`) identifies this host prefix with the encoded verifier configuration at time $t$. Since the total choice word has length $T+1$, at least one choice remains. Split the remaining word into its first bit and tail. The finishing-step fact (`Complexity.b2_verify_finish`) says that this next host step halts and writes the bit determined by whether the verifier's output is exactly $[\mathrm{true}]$. Since the verifier output is $[b]$, this bit is $b$, for either Boolean value. Once halted, the host remains in that configuration under the rest of the choices (`Turing.NDTM.runWith_of_halt`). Decomposing the choice word into prefix and suffix uses the run concatenation and one-bit recursion laws (`Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`), yielding the required halted state and output.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Complexity.b2_verify_run`, `Complexity.b2_verify_finish`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_of_halt`.
