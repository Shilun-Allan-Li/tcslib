<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_grow_right_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right extension of an encoded block

**Claim.** Running the simulator for $k$ steps from the forward-facing right-extension phase with counter zero reaches counter $k$, preserves $q$ and $s$, shifts the frontier to $z+k$, prepends the reversed encoded guard block to the left stack, and drops the first $k$ entries of the right stack, leaving the input-head position and output unchanged.

**Proof.** Let the generated word be the right-guard row determined by $s$; it has length $k$. For each counter $i<k$, the simulator writes the cell indexed by $i$, advances the frontier by one, and drops one entry from the right stack. The corresponding one-step identity for forward-facing moves is `sweepCfg_right_any`. Applying the iteration lemma `sweep_generate` for all $k$ symbols yields the total frontier shift $k$, the reversed generated block prepended to the left stack, and the right stack with its first $k$ entries removed. The full prefix of the generated word is the word itself, giving exactly the stated encoded guard block. The local transitions preserve $q$, $s$, the input-head position, and the output.

**Key facts.** `Turing.FinTM.sweepCfg_right_any`, `Turing.FinTM.sweep_generate`.
