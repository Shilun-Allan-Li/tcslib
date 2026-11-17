
/-! ### Pushforwards, products and acceptance of the uniform law -/

section Pushforward

variable {β : Type*} [Fintype β]

/-- **The uniform law is invariant under a bijection**: pushing the uniform distribution on `α`
through an equivalence `e : α ≃ β` gives the uniform distribution on `β`, `map e U_α = U_β`.
Framework glue, no textbook counterpart. -/
protected theorem FinDist.map_uniform_equiv [DecidableEq β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (FinDist.uniform α).map e = FinDist.uniform β := by
  classical
  apply FinDist.ext
  intro b
  rw [FinDist.map_apply]
  have hf : (univ : Finset α).filter (fun a => e a = b) = {e.symm b} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply b).symm)
    · rintro rfl
      exact e.apply_symm_apply b
  rw [hf, sum_singleton, FinDist.uniform_apply, FinDist.uniform_apply,
    Fintype.card_congr e]

/-- **Summing over a pushforward**: a weighted sum over the pushforward of `p` along `f` is the
sum of the composite over `p`, `∑ b, (map f p) b · g b = ∑ a, p a · g (f a)`.
Framework glue, no textbook counterpart. -/
protected theorem FinDist.sum_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (∑ b, (p.map f) b * g b) = ∑ a, p a * g (f a) := by
  classical
  simp only [FinDist.map_apply, sum_mul, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp only [if_neg (Ne.symm hba), zero_mul]
  · intro h
    exact False.elim (h (mem_univ _))

/-- **An acceptance probability is nonnegative**: `0 ≤ Pr_{x ← p}[D x = 1]`, i.e.
`0 ≤ p.probTrue D`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.probTrue_nonneg (p : FinDist α) (D : α → Bool) : 0 ≤ p.probTrue D := by
  rw [FinDist.probTrue_eq]
  exact sum_nonneg fun a _ => p.nonneg a

/-- **An acceptance probability is at most one**: `Pr_{x ← p}[D x = 1] ≤ 1`, i.e.
`p.probTrue D ≤ 1`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.probTrue_le_one (p : FinDist α) (D : α → Bool) : p.probTrue D ≤ 1 := by
  rw [FinDist.probTrue_eq, ← p.sum_prob]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => p.nonneg a)

/-- **The product of two uniform laws is uniform**: the independent pair of uniform samples of
`α` and `β` is the uniform distribution on `α × β`, `U_α × U_β = U_{α × β}`.
Framework glue, no textbook counterpart. -/
protected theorem FinDist.uniform_prod [Nonempty α] [Nonempty β] :
    (FinDist.uniform α).prod (FinDist.uniform β) = FinDist.uniform (α × β) := by
  apply FinDist.ext
  intro z
  rw [FinDist.prod_apply, FinDist.uniform_apply, FinDist.uniform_apply,
    FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

/-- **Acceptance under the uniform law is a count**: the probability that `D` accepts a uniform
sample of `α` is the number of accepted points divided by `|α|`,
`Pr_{U_α}[D = 1] = |{a : D a = 1}| · |α|⁻¹`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.uniform_probTrue [Nonempty α] (D : α → Bool) :
    (FinDist.uniform α).probTrue D =
      ((Finset.univ.filter (fun a => D a = true)).card : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
  rw [FinDist.probTrue_eq]
  simp only [FinDist.uniform_apply, sum_const, nsmul_eq_mul]

end Pushforward
