<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: size_eq_sum_cards -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Circuit size as a sum of layer cardinalities

**Claim.** For `F : FeedForward (Fin 2) (Fin n) out` with every layer a `Fintype`
(`[∀ i, Fintype (F.nodes i)]`),

`F.size = ∑ d : Fin F.depth, Fintype.card (F.nodes d.succ)`.

That is, the `Nat.card` of the sigma type of non-input nodes is the sum of the
cardinalities of the gate layers `1, …, F.depth`.

**Proof.**
* `rw [FeedForward.size, Nat.card_sigma]` unfolds `size` to
  `Nat.card (Σ d, F.nodes d.succ)` and splits it into `∑ d, Nat.card (F.nodes d.succ)`.
* `refine Finset.sum_congr rfl ?_; intro d _; simp` finishes: index sets agree, and each
  summand's `Nat.card` is replaced by `Fintype.card` using the ambient instance.

**Remark.** Purely bookkeeping — it converts the `Nat.card`-based definition of size
into the summation form the degree/error estimates are stated in. It is what lets
`gateCountBefore_depth_eq_size` identify the running gate count at full depth with
`F.size`, and thereby lets the three `…_size` theorems in this file restate the
error bounds of `CircuitDegree.lean` in terms of `F.size`.
