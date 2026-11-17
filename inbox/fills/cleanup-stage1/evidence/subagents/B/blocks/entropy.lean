
/-! ### Mixtures of sources -/

section Mixture

variable {α : Type*} [Fintype α]

/-- The **mixture** of `p` and `q` with weight `w ∈ [0, 1]`: the distribution that gives each
point `a` the convex combination `w · p(a) + (1 - w) · q(a)` (sample `p` with probability `w`,
`q` otherwise). Framework glue, no textbook counterpart. -/
protected noncomputable def FinDist.mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) : FinDist α where
  prob a := w * p a + (1 - w) * q a
  nonneg a := add_nonneg (mul_nonneg hw0 (p.nonneg a))
    (mul_nonneg (sub_nonneg.2 hw1) (q.nonneg a))
  sum_prob := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, p.sum_prob, q.sum_prob]
    ring

/-- **The point probability of a mixture** is its defining convex combination:
`mixture w p q a = w · p(a) + (1 - w) · q(a)`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.mixture_apply (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α)
    (a : α) : FinDist.mixture w hw0 hw1 p q a = w * p a + (1 - w) * q a :=
  rfl

/-- **A mixture of two `k`-sources is a `k`-source**: if every point has probability at most
`2^(-k)` under `p` and under `q`, then so under every mixture of them,
`IsSource k p → IsSource k q → IsSource k (mixture w p q)`, since a convex combination preserves
the common bound. Framework glue, no textbook counterpart. -/
protected theorem FinDist.mixture_isSource (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α)
    (k : ℝ) (hp : FinDist.IsSource k p) (hq : FinDist.IsSource k q) :
    FinDist.IsSource k (FinDist.mixture w hw0 hw1 p q) := by
  have hp' := (FinDist.hasMinEntropy_iff p k).1 (FinDist.isSource_iff_hasMinEntropy.1 hp)
  have hq' := (FinDist.hasMinEntropy_iff q k).1 (FinDist.isSource_iff_hasMinEntropy.1 hq)
  apply FinDist.isSource_iff_hasMinEntropy.2
  apply (FinDist.hasMinEntropy_iff _ _).2
  intro a
  rw [FinDist.mixture_apply]
  calc w * p a + (1 - w) * q a
      ≤ w * (2 : ℝ) ^ (-k) + (1 - w) * (2 : ℝ) ^ (-k) :=
        add_le_add (mul_le_mul_of_nonneg_left (hp' a) hw0)
          (mul_le_mul_of_nonneg_left (hq' a) (sub_nonneg.2 hw1))
    _ = (2 : ℝ) ^ (-k) := by ring

end Mixture
