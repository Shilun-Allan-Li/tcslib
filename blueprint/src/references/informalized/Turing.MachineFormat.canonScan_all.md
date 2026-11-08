<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonScan_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accepted scans leave only ones

**Claim.** If scanning $\alpha$ in format $F$ succeeds with returned suffix $tail$, then every bit of $tail$ is $1$.

**Proof.** Unfold the scan procedure and expose its successive successful parsing steps: pair decoding, the numeric and length guards, skipping the initial state and table, and the final check on the remaining suffix. The guards that fail are incompatible with a successful scan. Once the earlier parsing steps have succeeded, the scan can return only through its final branch, which requires that every bit of the remaining suffix is true. Hence $tail.all\ id=true$, as claimed.
