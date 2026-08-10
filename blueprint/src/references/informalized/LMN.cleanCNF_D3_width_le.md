<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: cleanCNF_D3_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a CNF does not increase its width

**Claim.** For every `ψ : CNF n`,
`CNF.width (cleanCNF_D3 ψ) ≤ CNF.width ψ`, where `CNF.width` is the `foldr max 0`
of the clause lengths.

**Proof.** By contradiction (`by_contra h_contra`), after `unfold CNF.width`.

1. `h_clean`: every clause `c'` of `cleanCNF_D3 ψ` is `dedupClauseVars c` for
   some `c ∈ ψ` (by definition of the `filter`/`map`), and
   `dedupClauseVars_length_le` gives `Term.width c' ≤ Term.width c`.
2. `h_width_le`: hence each such `c'` satisfies
   `c'.width ≤ List.foldr max 0 (ψ.map Term.width)` — an inner induction on the
   list shows any member's width is bounded by the `foldr max` over that list
   (`induction l <;> aesop`), and `le_trans` chains it with step 1.
3. `h_foldr_le`: if every element of a list `l : List ℕ` is `≤ B` then
   `List.foldr max 0 l ≤ B` (again `induction l <;> aesop`), with
   `B = CNF.width ψ`.
4. Instantiating step 3 at the clause-width list of `cleanCNF_D3 ψ` contradicts
   `h_contra`; `grind` finishes.

**Used in.** `exists_nice_cnf_of_cnf`, so that normalising a CNF never spoils the
width bound `≤ l` carried through the depth-3 argument.
