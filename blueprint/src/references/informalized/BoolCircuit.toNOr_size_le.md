<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNOr_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# OR-rooted normalization at most doubles the size

**Claim.** For every circuit `c : Circuit n`, `(c.toNOr).size ≤ 2 * c.size`:
converting to OR-rooted alternating normal form costs at most a factor two in
node count.

**Proof.** Immediate from the combined statement —
`(toNAnd_toNOr_size_le c).2`. A projection wrapper only.

**Remark.** Dual to `toNAnd_size_le`; the slack is the unary `NAndCircuit.node`
wrapper `Circuit.toNOr` inserts when an AND gate sits at an OR position.
