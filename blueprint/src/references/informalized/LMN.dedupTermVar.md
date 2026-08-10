<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: dedupTermVar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deduplicating a term by variable

**Definition.** For `t : Term n` (a list of literals),

`dedupTermVar t = t.foldr (fun l acc => if acc.any (fun l' => l'.var = l.var) then acc else l :: acc) []`

— scan `t` from the right, keeping a literal only if no already-kept literal has
the same variable. So `dedupTermVar t` is the sublist of `t` retaining, for each
variable, its **last** occurrence, in the original order. (The Lean docstring
says "whose variable already appeared earlier"; the `foldr` in fact keeps the
rightmost occurrence.)

The properties proved about it in the same file are the interface its two callers
need:

- `dedupTermVar_nodup` — the result is `Nodup`;
- `dedupTermVar_var_inj` — distinct kept literals have distinct variables
  (`l₁.var = l₂.var → l₁ = l₂`);
- `dedupTermVar_width_le` — `(dedupTermVar t).length ≤ t.length`;
- `dedupTermVar_preserves_term_eval` — `Term.eval (dedupTermVar t) x = Term.eval t x`
  provided `termHasContradiction t = false`;
- `dedupTermVar_preserves_clause_eval` — likewise for `CNF.evalClause`.

**Remark.** The non-contradiction hypothesis is essential for the two evaluation
lemmas: for `t = [x₁, ¬x₁]` deduplication would keep one literal and change the
value. That is why `cleanDNF`/`cleanCNF` filter with `termHasContradiction`
*before* mapping this function.

**Used in.** `cleanDNF` and `cleanCNF` (and, through them, the switching-lemma
hypothesis packaging in `switching_bernoulli_dtDepth_dnf_general` /
`_cnf_general`). Not referenced outside `CircuitHelpers.lean`.
