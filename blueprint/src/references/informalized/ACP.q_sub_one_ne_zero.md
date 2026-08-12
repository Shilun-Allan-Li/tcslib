<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: q_sub_one_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `q - 1 ≠ 0` for prime `q`

**Claim.** If `q` is prime (as a `Fact` instance) then `q - 1 ≠ 0`, with `-` the
truncated natural-number subtraction.

**Proof.** Two lines.

1. Extract `hq : Nat.Prime q` from the instance via `‹Fact (Nat.Prime q)›.out`.
2. `Nat.sub_ne_zero_of_lt` applied to `hq.one_lt : 1 < q`.

**Remark.** A deliberately granular helper: it exists only to discharge the
`n ≠ 0` side condition of `GaloisField.card` at the one place it is needed, so that
the exponent `q - 1` in `ModqField q = GaloisField p (q - 1)` is legitimate.

**Used in.** `natCard_modqField`.
