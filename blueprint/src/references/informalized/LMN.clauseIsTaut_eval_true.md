<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: clauseIsTaut_eval_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A tautological clause is satisfied by every assignment

**Claim.** Let `c : List (Literal n)` be a clause with `clauseIsTaut c`, i.e. `c`
contains two literals `l₁, l₂` with `l₁.var = l₂.var` and `l₁.neg ≠ l₂.neg`.
Then for every assignment `x : Fin n → Bool` the disjunction of `c` is true:
`c.any (fun l => l.eval x) = true`.

**Proof.**

1. Unpack the tautology witness with `obtain ⟨l₁, hl₁, l₂, hl₂, h_var, h_neg⟩ := h`,
   giving two clause members on the same variable with opposite polarity.
2. Case split on the two polarities (`cases h : l₁.neg <;> cases h' : l₂.neg`).
   Since `l₁.neg ≠ l₂.neg`, only the two mixed cases survive; in each, one of
   `l₁, l₂` is the positive and the other the negated literal on the same
   variable, so whichever value `x l₁.var` takes, one of them evaluates to
   `true` (`simp_all +decide [Literal.eval]`).
3. `grind` closes the remaining bookkeeping (membership witness feeding
   `List.any`).

**Used in.** `cleanCNF_D3_eval` — this is exactly why tautological clauses can be
deleted from a CNF without changing its value.
