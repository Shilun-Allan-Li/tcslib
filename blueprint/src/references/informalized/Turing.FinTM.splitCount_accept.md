<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitCount_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance read of the counting host

**Claim.** The overflow test is false and the counting-host configuration scans no input symbol exactly when $|s|+|c.output|=|w|$.

**Proof.** In the constructed configuration, the input head is at the saturated position corresponding to $j=|s|+|c.output|$. The position-reading fact (`splitPos_read`) says that this position scans a symbol precisely when $j<|w|$, and is blank otherwise. If $j<|w|$, the scanned-symbol test is not blank and the overflow test is false, so their conjunction is false; also $j\ne|w|$. If $j=|w|$, the scan is blank and overflow is false, so the conjunction is true. If $j>|w|$, the scan is blank but the overflow test is true, so the conjunction is false. These cases establish the asserted equivalence.

**Key facts.** `Turing.FinTM.splitPos_read`.
