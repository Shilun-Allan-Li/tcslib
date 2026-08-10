<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_aux_entries_from_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every aux entry index comes from an input literal

**Claim.** If `e ∈ (processClauseLits lits path ρ₀ σ).2.2.2`, then there is
`li ∈ lits` with `e.1 = li.2`. In words: the first components of the aux entries
emitted by `processClauseLits` are exactly (a sublist of) the clause positions
carried by the input literal list — the encoder never invents an index.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

1. `lits = []`: aux is `[]`, so `he` is impossible —
   `simp [processClauseLits] at he`.
2. `lits = hd :: tl`, `path = []`: aux is again `[]`, same discharge.
3. `lits = hd :: tl`, `path = p :: ps`: aux is `(hd.2, p.2) :: r.2.2.2`, so
   `simp only [processClauseLits, List.mem_cons] at he` and `rcases` splits `he`.
   - `e = (hd.2, p.2)`: take `li := hd`, membership by `.head _`, index by `rfl`.
   - `e` in the recursive aux: `obtain` the witness from `ih`, then relocate its
     membership with `List.mem_cons_of_mem`.

**Used in.** `processClauseLits_aux_ne_nonfree`,
`processClauseLits_aux_vars_free`, and `processClauseLits_aux_idx_lt` in
`TCSlib/BooleanAnalysis/Switching.lean` — all three lift a property of the input
literals to a property of the aux entries.
