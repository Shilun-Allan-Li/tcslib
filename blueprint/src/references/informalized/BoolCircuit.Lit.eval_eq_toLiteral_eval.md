<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: Lit.eval_eq_toLiteral_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Literal conversion preserves evaluation

**Claim.** For every `l : BoolCircuit.Lit n` and every assignment
`x : Fin n → Bool`, `l.eval x = l.toLiteral.eval x`.

**Proof.** Unfold both evaluators and the conversion with
`simp [BoolCircuit.Lit.eval, Literal.eval, BoolCircuit.Lit.toLiteral]`, then
`cases l.sign <;> simp`:

- `Lit.eval` tests `l.sign` and returns `x l.idx` when it is `true`;
  `Literal.eval` tests `l.neg` and returns `!x l.var` when it is `true`.
- `toLiteral` sets `var := l.idx` and `neg := !l.sign`, so the two `if`
  conditions are negations of each other and the branches line up in both cases
  (`sign = true` gives `x l.idx` on both sides, `sign = false` gives
  `!x l.idx`).

**Remark.** The content is entirely the polarity-convention flip in
`Lit.toLiteral`; it is stated separately so the convention is checked once rather
than re-derived inside each clause-level lemma. `foldr_and_lits_eq_term_eval`
and `foldr_or_lits_eq_clause_eval` prove the list-level analogues directly by
induction rather than by invoking this lemma, so within `TCSlib` it stands as the
pointwise statement of record.
