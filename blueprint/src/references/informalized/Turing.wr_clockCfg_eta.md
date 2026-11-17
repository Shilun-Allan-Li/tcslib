<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wr_clockCfg_eta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock-tape configuration decomposition

**Claim.** A configuration whose state is $(\mathrm{true},q)$ decomposes as the state-mapped clock configuration built from its first $K+1$ work tapes and their head positions, together with its original last tape and last head position.

**Proof.** Compare the two configurations field by field. Their states agree because the given state is $(\mathrm{true},q)$; the clock construction supplies $q$ and the state map tags it with $\mathrm{true}$. Their input positions and outputs are unchanged. For each work-tape index, split into the first $K+1$ indices and the final index: the smaller configuration uses the corresponding cast-successor entries of $d$, while the clock tape uses the last entry. The same split verifies equality of the head positions. Thus all configuration fields agree.
