<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_compare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Comparator Scan

**Claim.** If $y$ is the concatenation of $p$ and $v$, then the pair comparator started at the beginning of $v$, in comparison state with true flag and work word $u$, halts after $|v|+1$ steps and outputs the bit indicating whether $u=v$.

**Proof.** The scan invariant says that after $j$ steps, for each $j\le |v|$, the comparator is at the position just after the first $j$ bits of $v$, its work word is still $u$, and its flag records whether the first $j$ bits of $u$ agree with those of $v$ (`a3n_eq_scan`). Apply this with $j=|v|$. The head is then at the end marker of the input, and the flag is the truth value of equality between the length-$|v|$ prefixes of $u$ and $v$. The final transition compares that flag and the absence of a further bit of $u`; the characterization of word equality says that these conditions together are equivalent to $u=v$ (`a3n_eq_end`). Consequently the transition halts and emits exactly the singleton word containing the equality bit. The tape lookup at a natural-number position returns the corresponding list entry (`bufferTape_nat`), and the run-at-successor identity identifies this final transition with step $|v|+1$ (`runFrom_succ_eq_step'`).

**Key facts.** `Complexity.a3n_eq_scan`, `Complexity.a3n_eq_end`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
