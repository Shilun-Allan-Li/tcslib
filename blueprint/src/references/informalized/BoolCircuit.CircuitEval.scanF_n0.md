<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.scanF_n0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning an Initial Run of Ones

**Claim.** Starting the scan in phase $\mathrm{n0}$ with counter $r$, folding the scan update over a word ends in phase $\mathrm{sep}$ with counter increased by the length of its initial run of ones if the word contains a false bit; if it contains no false bit, it ends in phase $\mathrm{n0}$ with counter increased by the word's full length.

**Proof.** First observe that once the scan is in phase $\mathrm{sep}$, every subsequent bit leaves both phase and counter unchanged; this follows by induction over the remaining word. Now induct on the scanned word. For an empty word, the counter and phase are unchanged, as claimed. If the first bit is false, the update moves immediately from $\mathrm{n0}$ to $\mathrm{sep}$ without changing the counter, and the observation shows that the rest of the word has no effect; the initial run of ones has length zero. If the first bit is true, the update increases the counter by one and remains in $\mathrm{n0}$, so apply the induction hypothesis to the remaining word. The initial run length of the whole word is one plus that of the remainder. Whether the remainder contains a false bit determines which outcome applies; in either case the counter arithmetic gives the stated formula.
