<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: noisyInfluence_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Noisy influence at noise rate one is the ordinary influence

**Claim.** For `i : Fin n` and `f : BooleanFunc n`,
`noisyInfluence 1 i f = influence i f`.

**Proof.** Both sides are the same guarded sum over `S : Finset (Fin n)`:

- `noisyInfluence` unfolds to `∑ S, if i ∈ S then 1 ^ (S.card - 1) * f̂(S)² else 0`;
- `influence_eq_sum_fourier` (from `BooleanAnalysis/Basic.lean`) rewrites the
  right-hand side to `∑ S, if i ∈ S then f̂(S)² else 0`;
- `congr 1; ext S` reduces to the summands, and `split_ifs <;> simp` closes both
  branches — the only content is `1 ^ (S.card - 1) = 1`. ∎

**Note.** Dead declaration: `noisyInfluence_one` has no call sites anywhere in
the repository. It is the `ρ = 1` sanity check for the `noisyInfluence`
definition; the KKL argument in this file only ever uses the *inequality*
direction, `noisyInfluence_le_influence`.
