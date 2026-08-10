<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNAnd_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# AND-rooted normalization at most doubles the size

**Claim.** For every circuit `c : Circuit n`, `(c.toNAnd).size ≤ 2 * c.size`:
converting to AND-rooted alternating normal form costs at most a factor two in
node count.

**Proof.** Immediate from the combined statement —
`(toNAnd_toNOr_size_le c).1`. A projection wrapper only.

**Remark.** The factor two, rather than equality, comes from the
`.node false cs ↦ .node [NOrCircuit.node …]` case of `Circuit.toNAnd`, which
inserts one unary gate per root mismatch.
