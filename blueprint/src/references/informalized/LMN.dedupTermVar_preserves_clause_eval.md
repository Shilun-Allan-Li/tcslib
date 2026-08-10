<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: dedupTermVar_preserves_clause_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De-duplicating a non-tautological clause preserves its OR value

**Claim.** If `termHasContradiction t = false` then
`CNF.evalClause (dedupTermVar t) x = CNF.evalClause t x` for every `x` — the
disjunctive counterpart of `dedupTermVar_preserves_term_eval`.

**Proof.** `induction' t with l t ih generalizing x`; `nil` is `rfl`. In the
`cons` case split on `h : (dedupTermVar t).any (·.var = l.var)` and unfold
`dedupTermVar`.

1. **Head dropped.** Obtain the surviving witness `y` with `y.var = l.var`. The
   inner `have h_eval_eq : l.eval x = y.eval x` uses (i) the auxiliary fact
   that membership in the `foldr` output implies membership in the input list
   (`induction t <;> aesop`), so `y ∈ t`, and (ii) `hnc`, which then forbids
   `y.neg ≠ l.neg`. With equal literal values the omitted disjunct is
   redundant, and `rw [← ih x]` finishes after re-deriving the tail's
   non-contradiction from `hnc.2` (`grind`).
2. **Head kept.** `split_ifs` and `simp_all [CNF.evalClause]`; one branch is
   `tauto`, the other is `ih x` applied to the restriction of `hnc` to the
   tail.

**Used in.** `cleanCNF_eval`, hence in
`switching_bernoulli_dtDepth_cnf_general`.
