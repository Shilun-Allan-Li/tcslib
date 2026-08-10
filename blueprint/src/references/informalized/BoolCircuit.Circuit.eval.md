<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating a circuit at an assignment

**Definition.** `Circuit.eval : Circuit n → (Fin n → Bool) → Bool` is defined by
structural recursion on the three shapes of a circuit:

- `.lit l` evaluates to `l.eval x`, the literal's own value;
- `.node true cs` (AND gate) folds the children right-to-left with `&&` starting
  from `true`: `cs.foldr (fun c acc => c.eval x && acc) true`;
- `.node false cs` (OR gate) folds with `||` starting from `false`:
  `cs.foldr (fun c acc => c.eval x || acc) false`.

The empty-children cases follow from the fold seeds and are the expected ones:
an AND gate with no children is `true`, an OR gate with no children is `false`.

Since `Circuit n` is a nested inductive, the equation compiler generates the
recursion through `List`; reasoning about `eval` in the file goes via
`Circuit.ind` plus `List.foldr` lemmas rather than plain `induction`.

**Used in.** Every semantic statement in the `BoolCircuit` development: the
normalization correctness lemmas relating `Circuit.eval` to `NAndCircuit.eval`
and `NOrCircuit.eval`, the coercion lemmas for `NAndCircuit.toCircuit` /
`NOrCircuit.toCircuit`, and the LMN depth-2 bridges `depth2OrToDNF_eval` and
`depth2AndToCNF`'s counterpart, which compare `(Circuit.node false cs).eval x`
with the corresponding DNF/CNF evaluation.
