<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a DNF for the switching-lemma hypotheses

**Definition.** For `d : DNF n`,

`cleanDNF d = (d.filter (fun t => !termHasContradiction t)).map dedupTermVar`

— delete every term containing a variable in both polarities, then deduplicate
each surviving term by variable (`dedupTermVar`). Here
`termHasContradiction t` tests `∃ l₁ l₂ ∈ t, l₁.var = l₂.var ∧ l₁.neg ≠ l₂.neg`.

The four lemmas proved about it are exactly what
`switching_bernoulli_dtDepth_dnf` demands of its input:

- `cleanDNF_eval` — `(cleanDNF d).eval x = d.eval x`; the deleted terms were
  identically `false` (`contradiction_term_eval_false`) so they contributed
  nothing to the disjunction, and the kept ones are preserved by
  `dedupTermVar_preserves_term_eval`;
- `cleanDNF_width_le` — `(cleanDNF d).width ≤ d.width`, from
  `dedupTermVar_width_le` plus a `foldr max` bound;
- `cleanDNF_var_inj` and `cleanDNF_nodup` — every term is variable-injective and
  `Nodup`, inherited from `dedupTermVar_var_inj` / `dedupTermVar_nodup` via
  `List.mem_map`.

**Used in.** `switching_bernoulli_dtDepth_dnf_general` (same file), which is the
whole point: it drops the `var_inj`/`Nodup` side conditions from the DNF
switching lemma by normalizing the formula first. Also called directly in
`LMN/CompressionStep.lean` and `LMN/CircuitTreeManip.lean` when repackaging a
DNF witness.
