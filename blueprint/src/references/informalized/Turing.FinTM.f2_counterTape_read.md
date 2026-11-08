<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counterTape_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Counter Tape

**Claim.** For finite Boolean lists $u$ and $b$, the counter tape formed from their concatenation, read at the nonnegative position $|u|$, returns the first entry of $b$, or no entry when $b$ is empty.

**Proof.** The position $|u|$ is nonnegative, so the tape definition reduces to reading the concatenated list at index $|u|$. The list-index rule for a concatenation at the boundary between its two parts identifies this value with the entry of $b$ at index zero. If $b$ is empty there is no such entry; otherwise it is exactly the head of $b$.
