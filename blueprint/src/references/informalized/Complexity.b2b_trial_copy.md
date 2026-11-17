<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_trial_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy Trial

**Claim.** The copy phase finishes after $2|u|+2$ steps with $u$ appended to the stored word $x$ on the destination tape, without entering its done phase earlier, and with every work-head position bounded in absolute value by $|x|+|u|+1$.

**Proof.** The source tape begins with $u$ starting at position $|x|$, while the destination tape is distinct from it. The copy-run lemma (`copyTM_run_ofCfg`) describes the complete sweep: it copies each source symbol to the destination while moving both heads right, then rewinds both heads and enters the done phase. It also gives the destination tape’s final contents as the original tape updated by the copied word, and asserts that done is not reached at any earlier time. The buffer concatenation identity (`b2b_buffer_concat`) identifies those updated contents with the tape storing $x\mathbin{++}u$. The run lemma’s head-position bounds, together with the initial positions (the other designated heads are at the origin or at $|x|$), yield the stated bound for every tape and every time through completion.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Complexity.b2b_buffer_concat`.
