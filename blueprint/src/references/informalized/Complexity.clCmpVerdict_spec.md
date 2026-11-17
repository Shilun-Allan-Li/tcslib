<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmpVerdict_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparator Verdict Detects Equal Sums

**Claim.** For any four finite Boolean words, the comparator verdict after scanning their common maximum width is true exactly when their little-endian values have equal sums.

**Proof.** Set the scan length to the maximum word width. Every word then has length at most this number, so dropping that many bits leaves the empty word (`Complexity.clCmp_width`). The scanned-columns invariant (`Complexity.clCmpOrbit_spec`) says that the invariant at this length is equivalent to equality of the original sums. On empty residual words, the invariant’s remaining value equality compares just the two carry bits. The verdict is true precisely when the accumulated equality flag is true and these final carries agree; equality of their bit values is equivalent to equality of the bits themselves (`Complexity.clBit_eq`). Thus the verdict is true exactly when the original sums agree.

**Key facts.** `Complexity.clCmpOrbit_spec`, `Complexity.clCmp_width`, `Complexity.clBit_eq`.
