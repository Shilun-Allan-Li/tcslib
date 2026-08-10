<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dedupClauseVars_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deduplication makes a clause variable-injective

**Claim.** For any clause `c : List (Literal n)`, the list
`dedupClauseVars c` is variable-injective: if `l₁, l₂ ∈ dedupClauseVars c` and
`l₁.var = l₂.var`, then `l₁ = l₂`. (`dedupClauseVars c` is defined as
`c.pwFilter (fun l₁ l₂ => decide (l₁.var ≠ l₂.var))`.)

**Proof.**

1. `unfold dedupClauseVars` and expose the filter with
   `simp +decide [List.pwFilter]`.
2. Induct on the clause (`induction' c with x c ih`). The empty case is vacuous
   (`aesop`).
3. In the cons case, `pwFilter` keeps the head only when its variable differs
   from every variable already kept, so any two retained literals with equal
   `var` must be the same list entry; `grind` discharges this from the
   `pwFilter` equations and the induction hypothesis.

**Used in.** `cleanCNF_D3_var_inj`, hence one of the two "nice CNF" side
conditions (`≤`-width plus variable-injective, duplicate-free clauses) demanded
by the switching lemma.
