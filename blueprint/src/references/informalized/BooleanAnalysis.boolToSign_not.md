<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: boolToSign_not -->
<!-- origin: boolean-ch01-fourier-blr run cdca27e1b5fd verdict not_in_text (0.86) -->

# Negating a bit negates its sign

**Claim.** For every `b : Bool`, `boolToSign (!b) = -boolToSign b`, where
`boolToSign b = if b then -1 else 1` is the ±1 encoding of a bit.

**Proof.**

1. `cases b` splits into the two possible bits.
2. In each branch `simp [boolToSign]` evaluates both sides: `false ↦ 1` against
   `-(-1)`, and `true ↦ -1` against `-1`.

**Remark.** A two-case definitional identity, marked `@[simp]`. It is what makes
bit-flips turn into sign flips downstream: `chiS_neg` uses it under `simp_rw`,
and `BLR/BoolFourier.lean` re-exports it as `BoolToPM1_not`.
