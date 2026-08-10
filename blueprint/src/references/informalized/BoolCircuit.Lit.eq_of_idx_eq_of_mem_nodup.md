<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Lit.eq_of_idx_eq_of_mem_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Distinct variable indices force literals in a clause to coincide

**Claim.** Let `lits : List (Lit n)` have pairwise-distinct variable indices,
i.e. `(lits.map Lit.idx).Nodup`. If `l₁, l₂ ∈ lits` and `l₁.idx = l₂.idx`,
then `l₁ = l₂`. (In particular a clause of a normal-form circuit cannot
contain both `xᵢ` and `¬xᵢ`, nor a repeated literal.)

**Proof.**

1. Reformulate the `Nodup` hypothesis as injectivity of the indexing
   function: `List.nodup_iff_injective_get.mp hnd`.
2. Convert both memberships into positions: `List.mem_iff_get.mp h₁` and
   `List.mem_iff_get.mp h₂` give indices `i`, `j` with `lits.get i = l₁`,
   `lits.get j = l₂`.
3. `simp_all +decide` propagates these equalities through the `map`, turning
   `l₁.idx = l₂.idx` into equality of the two mapped entries.
4. Instantiate the injectivity at `i` and `j` (the `by simp` side goals just
   re-index into the mapped list), so `i = j`, and `aesop` concludes
   `l₁ = l₂`.

**Used in.** The `Nodup` invariant carried by `NAndCircuit.clause` /
`NOrCircuit.clause` — this is the form in which that invariant is consumed.
