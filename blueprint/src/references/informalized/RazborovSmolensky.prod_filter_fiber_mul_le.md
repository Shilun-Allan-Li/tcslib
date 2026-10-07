<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: prod_filter_fiber_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fiberwise counting bound on a filtered product

**Claim.** Let `α`, `β` be finite types, `P : α → Prop` and `Q : α → β → Prop`
decidable, and `C B : ℕ`. If every fiber over a good point obeys
`#{b | Q a b} * C ≤ B` for all `a` with `P a`, then

`#{z : α × β | P z.1 ∧ Q z.1 z.2} * C ≤ #{a | P a} * B`.

So a uniform per-fiber bound multiplies up to a bound on the whole filtered
product.

**Proof.**

1. The equivalence
   `e : {z // P z.1 ∧ Q z.1 z.2} ≃ Σ a : {a // P a}, {b // Q a.1 b}`
   regroups a constrained pair as a point of the base together with a point of
   its fiber; both inverses are `rfl` after `cases`.
2. `hcard`: chaining `Fintype.card_subtype`, `Fintype.card_congr e`,
   `Fintype.card_sigma` and a `Finset.sum_congr` gives
   `#{z | P z.1 ∧ Q z.1 z.2} = ∑ a : {a // P a}, #{b | Q a.1 b}`.
3. Multiply by `C` and push it inside the sum with `Finset.sum_mul`.
4. `Finset.sum_le_sum` with the hypothesis `hQ a.1 a.2` replaces each summand by
   `B`; `simp` evaluates the constant sum as `Fintype.card {a // P a} * B`, and
   `Fintype.card_subtype P` returns it to `#{a | P a} * B`.

**Used in.** `stepLayerFamily`, with `P r := ¬ PrevBad r` and `Q r t := GateBad r t`,
to bound the seeds that fail for the first time at the new layer.
