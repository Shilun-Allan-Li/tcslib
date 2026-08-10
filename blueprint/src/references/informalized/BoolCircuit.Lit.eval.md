<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Lit.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating a literal

**Definition.** A literal is the structure `Lit n` with fields `idx : Fin n` and
`sign : Bool`, where `sign = true` means the positive literal `xᵢ` and
`sign = false` means `¬xᵢ` (`deriving DecidableEq, Repr, Hashable`).

`Lit.eval (l : Lit n) (x : Fin n → Bool) : Bool` is the one-line

```
if l.sign then x l.idx else !x l.idx
```

It carries the `@[simp]` attribute, so proofs unfold it automatically rather than
citing it by name.

**Used in.** The base case of `Circuit.eval` (`.lit l, x => l.eval x`) and of
`NAndCircuit.eval` / `NOrCircuit.eval`, whose `clause` cases fold `l.eval x`
over the literal list. `BoolCircuit.Lit.eval_eq_toLiteral_eval` in
`LMN/NormalFormConversion.lean` shows it agrees with the LMN-side
`Literal.eval` under `Lit.toLiteral`, which is what lets the LMN DNF/CNF
machinery talk about `BoolCircuit` circuits.
