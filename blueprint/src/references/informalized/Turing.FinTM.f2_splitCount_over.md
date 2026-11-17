<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitCount_over -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow flag update

**Claim.** If the input head is at the position associated with $j$, then the current overflow flag or a blank scanned symbol occurs exactly when $|w|<j+1$.

**Proof.** By the input-reading property of the position associated with $j$ (`f2_splitPos_read`), the scanned symbol is $w[j]$ when $j<|w|$, and is blank otherwise. Split into these two cases. If $j<|w|$, then neither $|w|<j$ nor $|w|<j+1$ holds, and the scanned symbol is present, so both sides are false. If $j\ge |w|$, the scanned symbol is blank; also $|w|<j+1$, so both sides are true. This proves the equivalence.

**Key facts.** `Turing.FinTM.f2_splitPos_read`.
