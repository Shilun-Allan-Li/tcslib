<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay of the buffered word

**Claim.** During the replay phase, after any $j\le |a|$ steps the machine remains in replay state, its work head is at $j$, and its output is the first $j$ symbols of $a$ when `first` is true and empty otherwise.

**Proof.** Proceed by induction on $j$. At $j=0$, the configuration is the stated initial replay configuration, and the output identity follows in either flag case. For the successor step, assume the claim at $j$ and use the successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) to apply one transition. Since $j<|a|$, the buffer-at-natural-position identity (`Turing.FinTM.bufferTape_nat`) says the scanned work symbol is $a[j]$. The replay transition advances the work head by one, preserves the replay state and input position, and emits that symbol exactly when `first` is true. The input head stays fixed by the zero-movement fact (`Turing.moveInputPos_zero`). When the flag is true, appending $a[j]$ to the first $j$ symbols gives $a.take(j+1)$; when false, the output remains empty. This proves the induction step and hence the result for every $j\le |a|$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
