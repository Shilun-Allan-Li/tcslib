<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_after -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step anchor-free extension

**Claim.** A silent control transition from the seam configuration in state $q$ to state $r$ preserves the tape words and extends the anchor-free run through time $t+1$.

**Proof.** The uniform transition hypothesis says that in state $q$ the machine takes the same control action for every scanned-symbol tuple. On the seam configuration this gives exactly the seam configuration with state $r$ and unchanged tape words (`emitterP2_control`). The states $q$ and $r$ are both different from the anchor, so the one-step safety lemma applies: the run reaches this successor in one step and avoids the anchor at both times zero and one (`splitSafe_one`). Finally, concatenate this one-step run with the given run from $c$ to the seam configuration. The run composition and safety concatenation lemma yields the claimed configuration at time $t+1$ and anchor avoidance throughout (`splitSafe_join`).

**Key facts.** `Turing.FinTM.emitterP2_control`, `Turing.FinTM.splitSafe_one`, `Turing.FinTM.splitSafe_join`.
