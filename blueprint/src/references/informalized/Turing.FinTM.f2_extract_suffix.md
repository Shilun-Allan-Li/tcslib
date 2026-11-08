<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extracting a Suffix

**Claim.** With second extraction enabled, starting at the second-extraction state just after $pre$ and running for $|rest|+1$ steps halts just after $x=pre\mathbin{++}rest$, preserves the work tape and its head position, and appends $rest$ to the existing output.

**Proof.** Induct on the length of $rest$. For the empty suffix, the input head is at the end of the input, so its current input symbol is absent. The second-extraction transition therefore halts without moving either head or changing the work tape or output. For $rest=b::rest'$, the current input symbol is $b$. In the second-extraction state the machine outputs that bit and advances the input head, leaving the work tape unchanged. The remaining run is the induction hypothesis applied with prefix $pre++[b]$ and output $out++[b]$. Its output is $(out++[b])++rest'$, which is $out++(b::rest')$ by associativity of concatenation, and its final input position is just after all of $x$.

**Key facts.** `Turing.FinTM.f2_extractCfg_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`.
