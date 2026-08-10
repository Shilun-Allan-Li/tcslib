<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Literals of the switching-lemma layer

**Definition.** `Literal n` is a structure with two fields describing a literal
on `n` Boolean variables:

- `var : Fin n` — the variable index;
- `neg : Bool` — the polarity, with `neg = true` meaning the *negated* literal
  `¬x_var` and `neg = false` the positive literal `x_var`.

It `deriving DecidableEq`, which is what lets literals be filtered, deduplicated,
and compared inside terms and restrictions.

Its semantics are `Literal.eval l x = if l.neg then !x l.var else x l.var`.

**Remark.** Note the flag is *negation*, the reverse of `BoolCircuit.Lit.sign`
(where `true` is positive); the two literal types coexist in this file and are
bridged by `Lit.toLiteral` in `LMN/NormalFormConversion.lean`.

**Used in.** The base of the whole DNF/CNF stack: `Term n = List (Literal n)`,
hence `DNF n` and `CNF n`, and everything in the `SwitchingLemma2` development
that speaks of literals being fixed or killed by a restriction
(`Literal.fixedBy_eval_true`, `Literal.killedBy_eval_false`,
`Term.freeLiterals`).
