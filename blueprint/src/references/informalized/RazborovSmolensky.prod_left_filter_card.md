<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: prod_left_filter_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Filtering a product on the left factor multiplies the count by the right factor

**Claim.** For finite types `α`, `β` and a decidable predicate `P : α → Prop`,

`#{z : α × β | P z.1} = #{a : α | P a} * Fintype.card β`.

A counting identity with no circuit content: constraining only the first
coordinate leaves the second coordinate free.

**Proof.**

1. Build the explicit equivalence
   `e : {z : α × β // P z.1} ≃ {a : α // P a} × β`, sending `⟨(a,b), h⟩` to
   `(⟨a,h⟩, b)`; both round trips are `rfl` after `cases`.
2. `Fintype.card_subtype` (used backwards, via `symm`) turns the left-hand
   `Finset.filter` card into `Fintype.card {z // P z.1}`.
3. `Fintype.card_congr e` transports across the equivalence, `Fintype.card_prod`
   splits the product, and a second `Fintype.card_subtype P` converts back to a
   `filter` card.

**Used in.** `stepLayerFamily`, to count the seeds `(r, t) : A.Seed × Tail` whose
failure is inherited from the previous layer (the condition depends on `r` only).
