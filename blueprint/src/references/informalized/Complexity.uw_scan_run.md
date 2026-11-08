<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_scan_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run through a true input prefix

**Claim.** If $j\le |x|$, every bit of $x$ at an index below $j$ is true, and $j\le |w|$, then running on the prefix of $w$ of length $j$ from the initial configuration on $x$ yields the scan configuration at position $j$ with that prefix as buffer.

**Proof.** Proceed by induction on $j$. When $j=0$, the choice prefix is empty, so the run leaves the initial configuration unchanged; the initial-configuration identity (`uw_init`) identifies it with the scan configuration at position $0$ and empty buffer. For the successor case, write the prefix of length $j+1$ as the prefix of length $j$ followed by the next bit of $w$. The induction hypothesis identifies the configuration after the shorter prefix with the scan configuration at position $j$. The run on a concatenation processes the first part and then the second (`Turing.OracleNDTM.runWith_append`); the remaining one-bit run is one step (`uw_runWith_single`). Since the input bit at position $j$ is true, the scan-step result (`uw_scan_step`) advances to position $j+1$ and appends the next choice bit to the buffer. The length and bound hypotheses ensure the indicated input and choice bits exist and that the scan configurations are defined.

**Key facts.** `Complexity.uw_init`, `Turing.OracleNDTM.runWith_append`, `Complexity.uw_runWith_single`, `Complexity.uw_scan_step`.
