<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitCount_over -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow-flag update

**Claim.** At the saturated input-head position for $j$, the disjunction of $|w|<j$ and the blank-scan test is equivalent to $|w|<j+1$.

**Proof.** The position-reading identity (`splitPos_read`) says that the scan is blank exactly when $j\ge |w|$. If $j<|w|$, then the scan is a symbol and neither $|w|<j$ nor $|w|<j+1$ holds. If $j\ge |w|$, the scan is blank and the disjunction is true; in this case $|w|<j+1$ also holds. This proves the equivalence.

**Key facts.** `Turing.FinTM.splitPos_read`.
