<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_branch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance on an All-True Input

**Claim.** For Boolean strings $x,w$ with $|x|+3\le |w|$, the run on choice string $w$ halts, and its output is `[true]` exactly when every bit of $x$ is true and the prefix of $w$ of length $|x|$ belongs to $B$.

**Proof.** Split according to whether every bit of $x$ is true. In that case, split $w$ after its first $|x|$ bits and the next three bits. The scan-run result `uw_scan_run` shows that the machine has scanned the prefix and reached its scan configuration. The end-of-scan transition `uw_end_step` moves it to the query configuration with that prefix as its buffer. The tail behavior `uw_tail` says that the next two choices halt and output `[true]` exactly when the buffered word belongs to $B$ (otherwise the output is `[false]`). The remaining choice does not affect this conclusion, and once halted the machine stays halted (`runWith_of_halt`). Thus the claimed equivalence holds in this case. If some input bit is false, take the least index $j$ at which this happens. Every earlier bit is true, so `uw_scan_run` brings the machine to the scan configuration at $j$. The false-bit transition `uw_false_step` then halts and outputs `[false]`. Consequently the output cannot be `[true]`, and the condition that all input bits are true also fails. In both cases the run halts and the stated equivalence follows; `runWith_append` justifies composing the runs over the indicated segments of the choice string.

**Key facts.** `Complexity.uw_scan_run`, `Complexity.uw_end_step`, `Complexity.uw_tail`, `Complexity.uw_false_step`, `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt`.
