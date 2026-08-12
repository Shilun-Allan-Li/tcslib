<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: IsJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Being a junta on a set of coordinates

**Definition.** For `g : BooleanFunc n` and `J : Finset (Fin n)`,

```
IsJunta g J ↔ ∀ x y : BoolCube n, (∀ i ∈ J, x i = y i) → g x = g y
```

i.e. `g` depends only on the coordinates in `J`: any two inputs agreeing on `J`
receive the same value. A plain `def` into `Prop` with no proof content.

**Remark.** Stated extensionally ("agreement on `J` forces agreement of
values") rather than as "`g` factors through the restriction to `J`". That is
what makes it cheap to verify for a Fourier-truncated function: in
`lowDegreePart_depends_on_influential` the witness keeps only frequencies
`S ⊆ J`, so each surviving character `χ_S x = ∏ i ∈ S, boolToSign (x i)` is a
product over coordinates in `J`, and the junta property is discharged by
`Finset.prod_congr` with `congrArg boolToSign (hxy i …)` — no factorisation
object is ever built.

**Used in.** Three places, all in `KKL.lean`:
`lowDegreePart_depends_on_influential` (proved for the truncation restricted to
`influentialCoords f τ`), and the statement and proof of `friedgut_junta`,
where it is the conclusion's core — "`f` is `ε`-close to a junta on `J`". Note
the size of `J` is not part of this predicate; the bound `(J.card : ℝ) ≤ …` is
carried as a separate conjunct.
