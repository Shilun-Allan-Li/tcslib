<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_table_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Next Table Cell

**Claim.** For Boolean lists $l,r$ and a bit $b$, the buffer tape holding $l$ followed by $b$ and $r$ contains $b$ at integer position $|l|$.

**Proof.** The buffer-tape value at a natural-number position is the corresponding list lookup (`Turing.FinTM.bufferTape_nat`). At index $|l|$, the list lookup after the prefix $l$ is the head of the remaining list $b::r$, hence equals $b$.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
