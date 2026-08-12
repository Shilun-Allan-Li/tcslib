<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: cauchy_schwarz_influences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cauchy–Schwarz on the influence vector

**Claim.** For `f : BooleanFunc n`,

```
totalInfluence f ^ 2 ≤ n * ∑ i : Fin n, influence i f ^ 2
```

i.e. `I[f]² ≤ n · ∑_i Inf_i[f]²` — Cauchy–Schwarz applied to the `n`-vector of
coordinate influences against the all-ones vector.

**Proof.** Delegated to Mathlib.

1. `have h := @sq_sum_le_card_mul_sum_sq …` instantiates Mathlib's
   `(∑ i ∈ s, f i)² ≤ s.card * ∑ i ∈ s, f i ²` at `s = Finset.univ`,
   `f = fun i => influence i f`.
2. `simp only [Finset.card_univ, Fintype.card_fin, totalInfluence] at h ⊢`
   rewrites `Finset.univ.card` to `n` and unfolds `totalInfluence` into the sum
   it is definitionally equal to, matching both sides.
3. `exact_mod_cast h` bridges the `ℕ`-valued cardinality `n` and its real cast. ∎

**Used in.** Nothing — no other declaration in the repository references it.
It is "Step 15" of the file's KKL plan, intended to feed the variance step of
the hypercontractive argument; that argument stops at the `sorry` in
`KKL_balanced` (line 618), so this lemma is currently orphaned. Note the bound
runs the *unhelpful* direction for KKL — it lower-bounds `∑_i Inf_i²` by
`I[f]²/n`, and the pigeonhole actually used downstream is
`max_influence_from_sum_sq`.
