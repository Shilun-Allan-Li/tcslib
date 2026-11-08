<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitEmit_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix emission and halting

**Claim.** If the input word is the concatenation of a prefix and a suffix, then starting the split-emitting machine at the position determined by the prefix and running it for one more step than the suffix length emits that suffix, advances the input head to the end of the word, preserves the auxiliary head, and halts.

**Proof.** Proceed by induction on the suffix. If it is empty, the input head is at the end of the prefix, so the split-position reading rule says there is no input symbol (`f2_splitPos_read`). The machine’s transition from state $3$ on no symbol halts without changing the output or auxiliary head; its input position is already the end position. This proves the base case. For a suffix beginning with $b$, the split-position reading rule identifies the symbol under the input head as $b$. The transition in state $3$ moves the input head right, emits $b$, and remains in state $3$; the successor-position identity (`f2_splitPos_succ`) gives the configuration at the position for the prefix extended by $b$. Apply the induction hypothesis to the remaining suffix, with the prefix and output each extended by $b$. The run-length identity for iterated steps (`runFrom_succ_eq_step`) combines this first transition with the remaining run, and associativity of list concatenation gives the claimed final output.

**Key facts.** `Turing.FinTM.f2_splitPos_read`, `Turing.FinTM.f2_splitPos_succ`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
