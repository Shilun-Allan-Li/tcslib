<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.toCNF_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every clause of a converted CNF is variable-injective

**Claim.** Let `cs : List (NOrCircuit n)` with every child a clause,
`h_clauses : ∀ c ∈ cs, ∃ lits h, c = NOrCircuit.clause lits h`. Then for every
`t ∈ (NAndCircuit.node cs).toCNF` and all `l₁, l₂ ∈ t`, `l₁.var = l₂.var`
implies `l₁ = l₂`: no clause of the CNF mentions a variable twice.

**Proof.**

1. After `intros t ht l₁ hl₁ l₂ hl₂ hvar`, the auxiliary
   `obtain ⟨c, hc⟩ : ∃ c ∈ cs, t = NOrCircuit.clauseToTerm c` is obtained by
   `unfold NAndCircuit.toCNF at ht; aesop` — `toCNF` on a node is
   `cs.map NOrCircuit.clauseToTerm`, so membership is exactly this.
2. `rcases h_clauses c hc.1 with ⟨lits, h, rfl⟩` puts the child in clause form.
3. `exact NOrCircuit.clauseToTerm_var_inj lits h _ (by aesop) _ (by aesop) hvar`;
   the two `aesop` calls transport the memberships `hl₁`, `hl₂` across the
   rewriting of `t`.

**Used in.** Nothing yet — the CNF mirror of `NOrCircuit.toDNF_var_inj`.
