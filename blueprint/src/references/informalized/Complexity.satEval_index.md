<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Index Walk

**Claim.** Across the doubled encoding of $n$ true bits, the evaluator in phase $2$ advances the input offset by $2n$ and the certificate-head offset by $n$, preserving the phase and truth bits.

**Proof.** Induct on $n$. When $n=0$, the run has length zero and the starting and ending canonical configurations coincide. For the successor case, split off the first doubled true bit, so the input is a prefix followed by $[\mathrm{true},\mathrm{true}]$ and the remaining doubled unary word. The two-step rule (`Complexity.satEval_double`) consumes this pair in phase $2$, leaves the phase and truth bits unchanged, and advances the certificate head by one. The induction hypothesis processes the remaining $n$ pairs from the new configuration. Concatenate the two runs (`Turing.MultiTapeTM.runFrom_add`); their input advances total $2(n+1)$ positions and their certificate-head advances total $n+1$. The doubled-word length identity (`Complexity.satBits_length`) supplies the endpoint bound needed for the canonical configuration.

**Key facts.** `Complexity.satEval_double`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.satBits_length`.
