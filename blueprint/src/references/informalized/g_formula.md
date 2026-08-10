<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: g_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# g(M) as a single truncated difference

**Claim.** For isotropic `S` and `M : Finset (Fin n)`,
`g S M = (2 * M.card + finrank (S_M S (E_c M))) − (finrank S + finrank (S_M S M))`.
This is `g_expansion` with the two subtractions collected into one: the same
right-hand side, but grouped as a single truncated subtraction of a sum rather
than two successive subtractions.

**Proof.** One line: `convert g_expansion S hS M using 1; grind`. The
hypotheses and the ambient content are exactly those of `g_expansion`; the only
work is the `ℕ` identity `a − b − c = a − (b + c)` (`Nat.sub_sub`), which
`grind` discharges. No new mathematics.

**Remark.** The grouped form is the convenient one for the next step, because
`eq_tsub_iff_add_eq_of_le` converts a single `x = a − b` into the additive
equation `x + b = a` once `b ≤ a` is known.

**Used in.** `g_add_dims`, which does exactly that conversion and is in turn
used by `dim_ineq_aux` and `cleaning_dimension_identity`.
