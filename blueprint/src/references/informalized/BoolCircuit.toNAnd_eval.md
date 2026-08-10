<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNAnd_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# AND-rooted normalization preserves semantics

**Claim.** For every circuit `c : Circuit n` and assignment `x : Fin n → Bool`,
`(c.toNAnd).eval x = c.eval x`: normalizing into AND-rooted alternating normal
form computes the same Boolean function.

**Proof.** Immediate from the combined statement — `(toNAnd_toNOr_eval c x).1`.
The work is done there; this declaration exists only to expose the AND half
without the `toNOr` conjunct.

**Remark.** The mutual recursion of `Circuit.toNAnd` / `Circuit.toNOr` forces
the two halves to be proved simultaneously, hence this deliberately granular
projection wrapper.
