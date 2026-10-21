<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: foldr_or_lits_eq_clause_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A disjunction of circuit literals is the converted CNF clause

**Claim.** For `lits : List (Lit n)` and `x : Fin n → Bool`,

```
lits.foldr (fun l acc => l.eval x || acc) false = CNF.evalClause (lits.map Lit.toLiteral) x
```

i.e. the right-fold with `||` from `false` that `NOrCircuit.eval` uses on a base
clause agrees with `CNF.evalClause` (`List.any`) on the converted literal list.

**Proof.** `unfold CNF.evalClause`, then `induction lits <;> simp +decide [*]`,
then `unfold BoolCircuit.Lit.toLiteral; aesop`:

- Empty list: both sides are `false`.
- Cons: `simp` strips one `||` from each side and applies the induction
  hypothesis, reducing to `l.eval x = (Lit.toLiteral l).eval x`, which `aesop`
  settles by casing on `l.sign` after `toLiteral` is unfolded.

**Used in.** `NAndCircuit.node_eval_eq_toCNF_eval` (via `congr_arg` on the
remaining conjunction), and three times in the DNF-extraction argument of
`LMN/CircuitHelpers.lean` — the OR-side dual of
`foldr_and_lits_eq_term_eval`.
