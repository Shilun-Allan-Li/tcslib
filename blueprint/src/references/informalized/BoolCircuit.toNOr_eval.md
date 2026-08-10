<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNOr_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# OR-rooted normalization preserves semantics

**Claim.** For every circuit `c : Circuit n` and assignment `x : Fin n → Bool`,
`(c.toNOr).eval x = c.eval x`: normalizing into OR-rooted alternating normal
form computes the same Boolean function.

**Proof.** Immediate from the combined statement — `(toNAnd_toNOr_eval c x).2`.
This declaration only projects the `toNOr` half out of the conjunction.

**Remark.** Dual to `toNAnd_eval`; both are wrappers because the mutually
recursive normalizers cannot be handled by separate inductions.
