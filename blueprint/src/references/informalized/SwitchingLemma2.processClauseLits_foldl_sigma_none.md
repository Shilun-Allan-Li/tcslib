<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_foldl_sigma_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder's σ-foldl unfixes every variable the encoder fixed

**Claim.** Fix a term `t` and a literal list `lits` contained in `t.zipIdx`.
Suppose `v` is free under `ρ₀` but gets fixed by the encoder, i.e.
`(processClauseLits lits path ρ₀ σ).2.1 v ≠ none`. Then replaying the aux block
through the decoder's σ-update foldl — `fun σ e => match t.drop e.1 with
| [] => σ | l :: _ => Function.update σ l.var none` — from **any** starting
`σ_dec` yields `none` at `v`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`, `σ_dec`.

1. `lits = []` and `lits = hd :: tl` with `path = []`: `pcl.2.1 = ρ₀`, so `hset`
   contradicts `hfree` — `simp [processClauseLits] at hset; exact absurd hfree hset`.
2. `lits = hd :: tl`, `path = p :: ps`: `simp only [processClauseLits,
   List.foldl_cons]`, and `zipIdx_drop_spec t hd.1 hd.2 (hmem hd (.head _))`
   rewrites `t.drop hd.2` to `hd.1 :: drop_rest`, so the first foldl step is
   `Function.update σ_dec hd.1.var none`.
3. `by_cases heq : hd.1.var = v`.
   - Equal: after `subst`, the accumulator is already `none` at `v`, and
     `foldl_sigma_preserves_none` propagates that through the rest of the block.
   - Unequal: apply `ih` at `ps` with the updated `ρ₀`, `σ`, `σ_dec`; freeness of
     `v` and `hset` both survive the `Function.update` at `hd.1.var`
     (`Function.update_apply`, `if_neg`).

**Used in.** `roundtrip_inv_hC'` in `RoundTrip.lean` — the "encoder fixed it, so
the decoder frees it" half of the round-trip invariant.
