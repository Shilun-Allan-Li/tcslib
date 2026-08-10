<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanDNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a DNF preserves its value

**Claim.** For every `d : DNF n` and every `x : Fin n → Bool`,
`(cleanDNF d).eval x = d.eval x`, where
`cleanDNF d = (d.filter (fun t => !termHasContradiction t)).map dedupTermVar`
deletes the terms containing a variable in both polarities and then removes
repeated variables from each surviving term.

**Proof.** `unfold DNF.eval cleanDNF`, then `induction' d with t d ih`.

1. Empty DNF: `rfl` (both sides are `false`).
2. Cons `t :: d`: split on `by_cases h : termHasContradiction t`.
3. Term kept (`h : termHasContradiction t = false`): the filter keeps `t` as
   `dedupTermVar t`, and `dedupTermVar_preserves_term_eval` gives
   `Term.eval (dedupTermVar t) x = Term.eval t x`; `simp_all +decide` with that
   lemma plus `ih` closes the disjunction.
4. Term dropped (`h : termHasContradiction t = true`): the remaining goal is
   that `t`'s disappearance cannot change the `List.any`, discharged by
   `contradiction_term_eval_false t x h` (a term with `l₁.var = l₂.var` and
   `l₁.neg ≠ l₂.neg` evaluates to `false`), wrapped as
   `fun h' => absurd h' (by rw [contradiction_term_eval_false t x h]; decide)`.

One remark: the same syntactic test `termHasContradiction` is reused for CNFs in
`cleanCNF`, where it detects a *tautological* clause instead — dropping is sound
in both cases, but for the opposite reason (`false` under `∨`, `true` under `∧`).

**Used in.** `switching_bernoulli_dtDepth_dnf_general`, and in
`CircuitTreeManip.lean` / `CompressionStep.lean` wherever a DNF is normalised
before the switching lemma is applied.
