<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: tuple_fail_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Counting tuples that satisfy a predicate in every coordinate

**Claim.** For finite `ι` and `β` and a decidable predicate `P : β → Prop`,

`(univ.filter (fun f : ι → β => ∀ i, P (f i))).card = (univ.filter P).card ^ Fintype.card ι`.

A pointwise condition on a tuple is an independent condition per coordinate, so
the count is the per-coordinate count raised to the number of coordinates.

**Proof.** One explicit bijection, then a `calc` of cardinality rewrites.

1. `e : {f : ι → β // ∀ i, P (f i)} ≃ (ι → {b : β // P b})` with
   `toFun f i = ⟨f.1 i, f.2 i⟩` and `invFun g = ⟨fun i => (g i).1, fun i => (g i).2⟩`;
   `left_inv` is `intro f; cases f; rfl` and `right_inv` is `rfl`.
2. `Fintype.card_subtype` (used `symm`) rewrites the filtered card as
   `Fintype.card {f // ∀ i, P (f i)}`.
3. `Fintype.card_congr e` transports along the bijection, `Fintype.card_fun`
   turns the function type into a power, and `Fintype.card_subtype P` converts
   the base back into `(univ.filter P).card`.

**Status.** Currently unused — no other declaration references it. `count_bad_S`
reproves exactly this fact inline (its `htuple`, with the same `e`) for the seed
type `Fin ℓ → Finset (Fin width)`.
