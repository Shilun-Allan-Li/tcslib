<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmpOrbit_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparator Invariant After Scanned Columns

**Claim.** After $j$ columns have been scanned, the comparator invariant on the control registers and the words with their first $j$ bits dropped holds exactly when the four little-endian values satisfy the stated equality of sums.

**Proof.** Induct on the number $j$ of scanned columns. At $j=0$, the registers are initialized with zero carries and a true equality flag, and the invariant reduces directly to equality of the two sums of word values. For the successor step, apply the one-column update equivalence (`Complexity.clCmpUpdate_spec`) to the current registers and the words with their first $j$ bits dropped. Their heads are exactly the next scanned column, and their tails are the words with the first $j+1$ bits dropped. The update equivalence therefore identifies the invariant after the next scan with the invariant before it; the induction hypothesis identifies the latter with equality of the original sums.

**Key facts.** `Complexity.clCmpUpdate_spec`.
