<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: contradiction_term_eval_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A contradictory term is identically false

**Claim.** If `termHasContradiction t = true` then `Term.eval t x = false` for
every `x : Fin n → Bool`. Recall `termHasContradiction t` tests whether `t`
contains two literals on the same variable with opposite polarity, and
`Term.eval` is the AND (`List.all`) of the literals.

**Proof.**

1. Unfold `termHasContradiction` in `hc` and `grind` out the witnesses:
   `l₁, l₂ ∈ t` with `l₁.var = l₂.var` and `l₁.neg ≠ l₂.neg`.
2. Unfold `Term.eval` and case on `l₁.neg` and `l₂.neg`
   (`cases h : l₁.neg <;> cases h' : l₂.neg`). The two mixed-polarity cases are
   the live ones; `simp_all +decide [Literal.eval]` plus `grind` closes them,
   since one of the two literals asks for `x l₁.var = true` and the other for
   `x l₁.var = false`, so the conjunction has a false conjunct.

**Used in.** `cleanDNF_eval` — it justifies deleting contradictory terms from a
DNF, since a false disjunct does not change the disjunction.
