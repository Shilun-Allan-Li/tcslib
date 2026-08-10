<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.clauseToTerm_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A converted AND-clause has at most one literal per variable

**Claim.** Let `lits : List (Lit n)` with `h : (lits.map Lit.idx).Nodup`. Then
any two literals of `(NAndCircuit.clause lits h).clauseToTerm` that agree on
their variable are equal: `∀ l₁ ∈ …, ∀ l₂ ∈ …, l₁.var = l₂.var → l₁ = l₂`. This
is the "no variable repeated with either sign" condition the switching-lemma
`Term` interface expects.

**Proof.**

1. `simp [NAndCircuit.clauseToTerm]` turns membership in the converted term into
   membership in `lits` (the term is `lits.map Lit.toLiteral`), and
   `unfold BoolCircuit.Lit.toLiteral` exposes each literal as `⟨a.idx, !a.sign⟩`,
   so the hypothesis `l₁.var = l₂.var` becomes `a.idx = a_1.idx` for source
   literals `a, a_1 ∈ lits`.
2. `have ha_eq : a = a_1` by `by_contra`: from `h`, `List.pairwise_map.mp h`
   gives that distinct members of `lits` have distinct indices — used through
   `.forall (fun _ _ hh => hh.symm)` to get both orders of the pair — which
   contradicts `a.idx = a_1.idx`.
3. `rw [ha_eq]` then makes the two converted literals syntactically identical.

**Used in.** `NOrCircuit.clauseToTerm_var_inj` (by `convert`) and
`NOrCircuit.toDNF_var_inj`, the DNF-level version of the same side condition.
