<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Lit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Literals of the BoolCircuit layer

**Definition.** `BoolCircuit.Lit n` is a one-field-pair structure describing a
literal on `n` Boolean variables:

- `idx : Fin n` — the variable index;
- `sign : Bool` — the polarity, with `sign = true` meaning the positive literal
  `xᵢ` and `sign = false` meaning `¬xᵢ`.

It `deriving DecidableEq, Repr, Hashable`, so literals can be compared,
printed, and used as keys.

Its semantics live in the companion definition
`Lit.eval l x = if l.sign then x l.idx else !x l.idx` (a `@[simp]` lemma by
declaration).

**Remark.** This is the circuit layer's own literal type, deliberately separate
from the switching-lemma `Literal n` in the same file, and with the *opposite*
flag convention (`Lit.sign = true` is positive, `Literal.neg = true` is
negated). `Lit.toLiteral` in `LMN/NormalFormConversion.lean` bridges the two.

**Used in.** Every `BoolCircuit` construction: the `Circuit.lit` leaves, the
`clause` constructors of `NAndCircuit` / `NOrCircuit` (whose `Nodup` invariant
is stated on `lits.map Lit.idx`), and the normalization maps `toNAnd` / `toNOr`.
