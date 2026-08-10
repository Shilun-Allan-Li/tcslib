<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: and_of_gates_has_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# AND of shallow restricted gates is one nice narrow CNF

**Claim.** Let `gates : Fin s₂ → DNF n`, `ρ₁ : Restriction n`, and suppose
`dtDepth (restrictFn (gates i).eval ρ₁) ≤ l` for every `i`. Then there is
`Ψ : CNF n` with `CNF.width Ψ ≤ l`, every clause `Nodup`, every clause
variable-injective, and
`CNF.eval Ψ x = (Finset.univ : Finset (Fin s₂)).val.toList.all (fun i => restrictFn (gates i).eval ρ₁ x)`
for all `x` — the AND over all gates.

**Proof.**

1. First get a plain (not yet hygienic) CNF: `apply compression_and_of_cnfs`
   to the list `Finset.univ.val.toList.map (fun i => restrictFn (gates i).eval ρ₁)`;
   its hypothesis "each member has a width-`l` CNF" is
   `all_gates_have_small_cnf gates l ρ₁ h_gates` after `simp +zetaDelta`.
   Concatenating the per-gate clause lists gives `Ψ` with `CNF.width Ψ ≤ l`.
2. Then clean it: `exists_nice_cnf_of_cnf Ψ` yields `Ψ'` with
   `CNF.width Ψ' ≤ CNF.width Ψ`, the same evaluation, `Nodup` clauses and
   variable-injective clauses.
3. Package `⟨Ψ', le_trans hΨ'.1 hΨ.1, …⟩`, transporting the evaluation with
   `simpa [hΨ.2] using hΨ'.2.1 x`. ∎

**Note.** Step 1 is the depth-reduction move (AND-of-CNFs is a CNF); step 2 only
restores the switching-lemma side conditions. Inherits the `sorry` in
`dedupClauseVars_eval_of_not_taut` through `exists_nice_cnf_of_cnf`.

**Used in.** `depth3_restricted_has_nice_cnf`, which converts the `List.all`
form into `restrictFn f ρ₁` for an `f` that is the AND of the gates.
