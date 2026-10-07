<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: exists_good_parameter_of_pointwise_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A pointwise failure bound yields one good parameter

**Claim.** Let `α`, `β` be finite types with `β` nonempty, let
`Fail : α → β → Prop` be decidable, and let `C B : ℕ`. If for every `a : α` the
number of `b` with `Fail a b` satisfies
`#{b | Fail a b} * C ≤ B * Fintype.card β`, then there exists a single `b : β`
with `#{a | Fail a b} * C ≤ B * Fintype.card α`. Averaging in the other index: if
no point fails for more than a `B / C` fraction of parameters, some parameter
fails at no more than a `B / C` fraction of points.

**Proof.** By contradiction (`by_contra!`), so `h b` gives the strict reverse
inequality for every `b`.

1. Double counting: `∑ b, #{a | Fail a b} = ∑ a, #{b | Fail a b}` via
   `simp only [card_filter]` and `Finset.sum_comm`. Multiplying through by `C`
   (`Finset.sum_mul` twice) gives the same identity for the `* C` sums (`hsumC`).
2. Lower bound `hlt`: `Fintype.card β * (B * Fintype.card α)` is the constant sum
   `∑ b, B * Fintype.card α`, which is `< ∑ b, #{a | Fail a b} * C` by
   `Finset.sum_lt_sum` — each term is `≤` by `h b`, and one witness `b₀` from
   `Nonempty β` is strict.
3. Upper bound `hle`: rewrite by `hsumC`, apply `Finset.sum_le_sum` with the
   hypothesis `hpoint a` termwise, then collapse the constant sum to
   `Fintype.card α * (B * Fintype.card β)`.
4. Chaining the two and commuting the product with `ring` yields
   `Fintype.card β * (B * Fintype.card α) < itself`, refuted by `Nat.lt_irrefl`.

**Remark.** Purely combinatorial — no polynomials or fields appear; the statement
is the reusable averaging step.
