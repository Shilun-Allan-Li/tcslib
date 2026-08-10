<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: foldr_and_lits_eq_term_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A conjunction of circuit literals is the converted term

**Claim.** For `lits : List (Lit n)` and `x : Fin n → Bool`,

```
lits.foldr (fun l acc => l.eval x && acc) true = Term.eval (lits.map Lit.toLiteral) x
```

i.e. the right-fold with `&&` from `true` that `NAndCircuit.eval` uses on a base
clause agrees with `Term.eval` (`List.all`) on the converted literal list.

**Proof.** `induction lits <;> simp_all +decide [Term.eval]`, then
`unfold BoolCircuit.Lit.toLiteral; aesop`:

- Empty list: both sides are `true` (`foldr` returns the seed, `List.all` on
  `[]` is `true`).
- Cons: `simp_all` peels one `&&` off each side and rewrites with the induction
  hypothesis, leaving the head comparison `l.eval x = (Lit.toLiteral l).eval x`;
  unfolding `toLiteral` and casing on `l.sign` (`aesop`) closes it.

**Used in.** `NOrCircuit.node_eval_eq_toDNF_eval`, where it is applied backwards
(`rw [← foldr_and_lits_eq_term_eval]`) to turn each `NAndCircuit.clause` child of
a depth-2 OR-node into the corresponding DNF term.
