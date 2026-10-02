<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_aux_ne_nonfree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# No aux entry decodes to a target variable v

**Claim.** Fix a term `t` and a literal list `lits` all of whose entries occur in
`t.zipIdx`, and suppose no literal in `lits` has variable `v`. Then for every aux
entry `e ∈ (processClauseLits lits path ρ₀ σ).2.2.2`, the literal the decoder
reads at that index — i.e. the head `l` of `t.drop e.1 = l :: rest` — satisfies
`l.var ≠ v`. This is the encoder-side statement that the decoder's foldl will not
touch `v`.

**Proof.** Fix `e`, `l`, `rest` and `hdrop : t.drop e.1 = l :: rest`.

1. `processClauseLits_aux_entries_from_lits` gives `li ∈ lits` with `e.1 = li.2`.
2. `hmem li hli` places `li` in `t.zipIdx`, so `zipIdx_drop_spec` yields
   `t.drop li.2 = li.1 :: rest'`.
3. Rewriting `hidx` and then `hdrop'` into `hdrop` makes both sides `cons`es of
   the same list; `List.cons.inj` gives `l = li.1`.
4. `rw [this]` turns the goal into `li.1.var ≠ v`, which is `hne_var li hli`.

**Used in.** `RoundTrip.lean` (`roundtrip_inv_hC'` and `roundtrip_inv_hD'`),
where it supplies the `hne` hypothesis of `foldl_sigma_stable` /
`foldl_rho_stable`.
