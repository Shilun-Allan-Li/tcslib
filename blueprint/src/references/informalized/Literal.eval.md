<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Literal.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating a literal

**Definition.** `Literal.eval (l : Literal n) (x : Fin n → Bool) : Bool` reads
the assigned bit at the literal's variable and flips it when the literal is
negated:

```
Literal.eval l x = if l.neg then !x l.var else x l.var
```

That is: `x l.var` for a positive literal (`l.neg = false`), and `!x l.var` for
a negated one (`l.neg = true`). A plain one-line definition with no recursion and
no hypotheses; unfolding it is the entire content of most literal-level steps.

**Remark.** It is *not* marked `@[simp]` here, unlike its circuit-layer
counterpart `BoolCircuit.Lit.eval` — proofs about it typically go through
`simp [Literal.eval]` or `unfold Literal.eval` explicitly.

**Used in.** `Term.eval` (`t.all (fun l => l.eval x)`) and
`CNF.evalClause` (`t.any (fun l => l.eval x)`), and therefore transitively in
`DNF.eval` and `CNF.eval`; also directly in the restriction lemmas
`Literal.fixedBy_eval_true` and `Literal.killedBy_eval_false`.
