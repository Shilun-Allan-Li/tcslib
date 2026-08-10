<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: sign_mul_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Sign times value is absolute value

**Claim.** For `x : ℝ`, `Real.sign x * x = |x|`.

**Proof.** Trichotomy on `x` (`rcases lt_trichotomy x 0`), three one-liners:

- `x < 0`: `Real.sign_of_neg hx` and `abs_of_neg hx` turn the goal into
  `(-1) * x = -x`, closed by `ring`.
- `x = 0`: `simp [Real.sign_zero]`.
- `0 < x`: `Real.sign_of_pos hx`, `abs_of_pos hx` and `one_mul`. ∎

**Note.** Dead declaration: `private` and referenced nowhere in the repository.
`holder_sharpness`, the proof that would naturally use it, instead unfolds
`Real.sign` and closes each branch with `split_ifs`; its companion
`abs_sign_eq_one` is unused for the same reason.
