<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: noisyInfluence_power_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Noisy influence is bounded by the influence

**Claim.** For `i : Fin n`, `f : BooleanFunc n` with `isPmOne f`, and `0 < ρ ≤ 1`,

`noisyInfluence ρ i f ≤ influence i f`.

**Proof.** One line: `exact noisyInfluence_le_influence i f ρ (le_of_lt hρ0) hρ1`.
That lemma proves the same inequality from `0 ≤ ρ` by comparing the two Fourier
sums termwise (`influence_eq_sum_fourier`, then `pow_le_one₀` on the damping
factor `ρ^(|S|-1)`); this wrapper only weakens `0 < ρ` to `0 ≤ ρ`.

**Caveat — the name overstates the content.** The "power bound" the file's
comments describe is the log-convexity estimate
`noisyInfluence ρ i f ≤ (influence i f)^ρ`, which is the nontrivial ingredient of
KKL. What is actually proved here is the trivial monotonicity bound
`≤ influence i f`. Two signs of the gap: the `±1` hypothesis is bound as `_hf` and
never used, and the source comment above the lemma says as much ("we state a
weaker but sufficient version" — it is not in fact sufficient).

**Status.** Unused; it appears only in comments. `KKL_balanced`'s hard case
(`Real.log n / 30 > totalInfluence f`) is a **`sorry`** at `KKL.lean:618`
("SORRY #19d"), and its TODO explicitly blocks on strengthening this lemma to
log-convexity. So the declaration typechecks, but the theorem it exists to serve
is not proved.
