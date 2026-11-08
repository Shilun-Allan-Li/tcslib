<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_tail_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail scan reaches its exit state

**Claim.** The tail-reading computation safely scans the suffix $w$ against the remaining binary word for $k$, updating the comparison flag and last-bit information, and reaches the corresponding exit configuration with registers cleared and heads at zero.

**Proof.** Induct on the input suffix $w$. When $w$ is empty, one read finds no input bit. The machine's tail transition uses the remaining counter word and the last-bit information to determine the exit value; the symbol-on-counter lemma identifies the symbol read with the head of the binary word after dropping $q$ bits (`access_symbol`). The one-step transition is a safe path (`access_step`), and the return routine restores the counter head and clears the input-position register (`access_return`). The counter word stays within the safety bound because its length is at most the length of the binary word for $|y|+1$ (`length_bits_mono`).

For $w=b::w'$, read $b$ and update the comparison flag according to whether the current counter bit matches $b$. The transition moves the counter head right exactly when a counter bit remains; choosing $q'=\min(q+1,|\mathrm{bits}(k)|)$ makes the new head position agree with that movement and makes the remaining counter word the tail of the previous one. The transition and its movement are justified by `access_step` and `access_move`; then the pointer-increment path advances the input scan while preserving safety (`access_inc_pointer`). The induction hypothesis applies to $w'$ with the updated comparison flag, last bit $b$, and position $q'$. Composing these paths gives the required exit configuration.

**Key facts.** `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.access_read`, `Complexity.LogProg.access_symbol`, `Complexity.LogProg.access_step`, `Complexity.LogProg.access_move`, `Complexity.LogProg.access_return`, `Complexity.LogProg.access_inc_pointer`.
