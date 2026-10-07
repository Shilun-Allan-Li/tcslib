<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: finite_cover_by_hamming_balls_card_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Union bound: covering a function space by Hamming balls

**Claim.** Let `α`, `Cand` be finite types, `β` have decidable equality with `α → β`
finite, and `center : Cand → α → β`. If every ball has size at most `B`,

`#{f : α → β | #{a | center c a ≠ f a} ≤ e} ≤ B` for all `c : Cand`,

and every function lies in some ball, `∀ f, ∃ c, #{a | center c a ≠ f a} ≤ e`, then

`Fintype.card (α → β) ≤ Fintype.card Cand * B`.

**Proof.** By an explicit injection rather than a counting rearrangement.

1. `Classical.choose` on the cover hypothesis picks `chooseC f : Cand` with the ball
   membership `hchoose f` given by `Classical.choose_spec`.
2. Let `Enc = Σ c : Cand, {f : α → β // #{a | center c a ≠ f a} ≤ e}` and
   `enc f = ⟨chooseC f, ⟨f, hchoose f⟩⟩`. This is injective because the second
   component recovers `f`: `congrArg (fun z : Enc => z.2.1)`. Hence
   `Fintype.card (α → β) ≤ Fintype.card Enc` by `Fintype.card_le_of_injective`.
3. Bound `Fintype.card Enc` by a `calc`: it is `∑ c, Fintype.card {f // …}` (`simp` on
   the sigma type), each summand equals the corresponding filtered-finset card by
   `Fintype.card_subtype`, then `Finset.sum_le_sum` with `hball` replaces every
   summand by `B`, and `simp` evaluates `∑ _ : Cand, B = Fintype.card Cand * B`.
4. `le_trans` of the two bounds.

**Remark.** Stated abstractly over `α`, `β`, `Cand` with no reference to polynomials
or cubes — this is the pigeonhole step of Smolensky's final counting line, isolated.

**Used in.** `rootCube_counting_obstruction`, instantiated at `α = rootCube ω n`,
`β = K`, `center c x = (poly c).eval x.1`.
