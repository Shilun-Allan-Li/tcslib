<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: q_pow_qary_entropy_simp' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Closed form for q^H_q(p), power-notation variant

**Claim.** For `2 ≤ q` and `0 < p < 1`,
`q ^ (qaryEntropy q p) = (q - 1)^p · p^(-p) · (1 - p)^(-(1-p))`, stated with the
`^` heterogeneous power notation on `↑q` rather than with an explicit
`Real.rpow q _`.

**Proof.** Immediate from `simpa using q_pow_qary_entropy_simp hq hp`: the two
statements differ only by the `Real.rpow`/`^` coercion that `simp` normalises.

**Note.** A deliberately granular notation-bridging lemma — it carries no
mathematical content beyond `q_pow_qary_entropy_simp`, and exists so downstream
`rw`s can fire against whichever form the ambient goal happens to display.

**Used in.** The same ball-counting and Gilbert–Varshamov estimates as
`q_pow_qary_entropy_simp`, wherever the goal presents `↑q ^ _` rather than
`Real.rpow ↑q _`.
