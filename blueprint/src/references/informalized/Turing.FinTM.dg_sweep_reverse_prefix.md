<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_sweep_reverse_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep Prefix Position

**Claim.** Under the local left-moving visit rule, after any $u\le |as|$ steps from the reflected zipper configuration whose right list begins with the encodings of $as$, the work head is at $z-u$.

**Proof.** Split $as$ into its first $u$ entries and its remaining suffix. Apply the full backward-sweep result (`sweep_run_reverse`) to the prefix, with the suffix and the original right remainder left untouched. The transition hypothesis ensures that each of the $u$ entries is visited, rewritten according to the local rule, and followed by a leftward move. Hence the head is at $z-|as.take(u)|$. The bound $u\le |as|$ makes the prefix length exactly $u$, giving $z-u$.

**Key facts.** `Turing.FinTM.sweep_run_reverse`.
