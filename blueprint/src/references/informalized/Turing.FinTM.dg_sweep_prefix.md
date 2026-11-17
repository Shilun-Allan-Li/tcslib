<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_sweep_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Sweep Prefix Position

**Claim.** Under the local right-moving visit rule, after any $u\le |as|$ steps from the zipper configuration whose right list begins with the encodings of $as$, the work head is at $z+u$.

**Proof.** Split $as$ into its first $u$ entries and the remaining suffix. Apply the full forward-sweep result (`sweep_run`) to the length-$u$ prefix, taking the suffix, followed by the original right remainder, as the untouched right list. The transition hypothesis ensures that each of these $u$ entries is visited, rewritten according to the local rule, and followed by a rightward move. Thus after the prefix sweep the head is at $z+|as.take(u)|$. Since $u\le |as|$, the prefix has length $u$, so this position is $z+u$.

**Key facts.** `Turing.FinTM.sweep_run`.
