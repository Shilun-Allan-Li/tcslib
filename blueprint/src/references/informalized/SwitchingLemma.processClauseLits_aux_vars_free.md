<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_aux_vars_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Aux entries point at variables free under ρ₀

**Claim.** Fix a term `t` and a literal list `lits` all of whose entries occur in
`t.zipIdx` and all of whose variables are free under `ρ₀` (`ρ₀ p.1.var = none`).
Then for any aux entry `e ∈ (processClauseLits lits path ρ₀ σ).2.2.2`, the
literal the decoder reads at that index — the head `l` of `t.drop e.1 = l :: rest`
— also has `ρ₀ l.var = none`.

**Proof.** Same three-step index-chase as `processClauseLits_aux_ne_nonfree`,
with `hfree` in place of `hne_var`.

1. `processClauseLits_aux_entries_from_lits` produces `li ∈ lits` with
   `e.1 = li.2`.
2. `zipIdx_drop_spec t li.1 li.2 (hmem li hli)` gives
   `t.drop li.2 = li.1 :: rest'`.
3. Rewriting `hidx` and `hdrop'` into `hdrop` and applying `List.cons.inj` gives
   `l = li.1`; then `rw [this]; exact hfree li hli`.

**Note.** Currently unused elsewhere in the library — it is the `ρ₀`-freeness
twin of `processClauseLits_aux_ne_nonfree`, kept for symmetry.
