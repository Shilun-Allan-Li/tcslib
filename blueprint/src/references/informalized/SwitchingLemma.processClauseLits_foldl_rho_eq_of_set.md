<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_foldl_rho_eq_of_set -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# ρ₀-foldl agreement without matching initial values

**Claim.** Same conclusion as `processClauseLits_foldl_rho_eq` — the decoder's
ρ₀-update foldl over `(processClauseLits lits path ρ₀ σ).2.2.2`, started from an
arbitrary `ρ₀_dec`, agrees with `(processClauseLits lits path ρ₀ σ).2.1` at `v` —
but the hypothesis `ρ₀ v = ρ₀_dec v` is replaced by: `v` is free under `ρ₀`
(`ρ₀ v = none`) and the encoder fixes it (`pcl.2.1 v ≠ none`). Again `lits` must
be contained in `t.zipIdx`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`, `ρ₀_dec`.

1. `lits = []`, and `lits = hd :: tl` with `path = []`: `pcl.2.1 = ρ₀`, so `hset`
   contradicts `hfree` — `simp [processClauseLits] at hset; exact absurd hfree hset`.
2. `lits = hd :: tl`, `path = p :: ps`: `simp only [processClauseLits,
   List.foldl_cons]` plus `zipIdx_drop_spec` exposes the shared first update at
   `hd.1.var`, then `by_cases heq : hd.1.var = v`.
   - Equal: both `ρ₀` and `ρ₀_dec` now read `some p.2` at `v`
     (`Function.update_apply`, `if_pos`), so the initial values *do* agree and
     `processClauseLits_foldl_rho_eq` finishes the remaining block.
   - Unequal: apply `ih`; `hfree` and `hset` transport across the update
     (`if_neg (Ne.symm heq)`).

**Used in.** `roundtrip_inv_hD'` in `RoundTrip.lean` — the case of the round-trip
invariant where the decoder's ρ₀ has drifted from the encoder's outside `v`.
