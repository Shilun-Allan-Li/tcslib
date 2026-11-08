<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Modules_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Bound for the Module Bank

**Claim.** Each of the five machines in the module bank uses at most $1+k_S+k_J+k_E+k_I$ work tapes.

**Proof.** The five possible indices select, in order, the release-wrapped input copier, $S$, $J$, $E$, and $I$. The first machine has one work tape: its stop wrapper keeps the copier's tape count. Each of the other four machines has respectively $k_S,k_J,k_E,k_I$ work tapes. In every case the selected count is bounded by $1+k_S+k_J+k_E+k_I$, since all tape counts are natural numbers.
