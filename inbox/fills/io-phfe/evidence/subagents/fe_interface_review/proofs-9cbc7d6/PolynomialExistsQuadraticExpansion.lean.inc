/-- A polynomial with public degree at most d and private degree at most two has
coefficients on padded public tuples and ordered padded private pairs. The same
coefficients work for all variable values. This is the algebraic representation
underlying [GJLS21, Section 9, printed p.58].

**Proof sketch.** Apply the padded-monomial representation separately to the public
and private exponents of each supported monomial. Choose one public tuple and one
private ordered pair for each support element. Collect coefficients by those finite
fibres. Expand evaluation with the published monomial-sum formula, interchange the
finite sums, and select the unique assigned tuple and pair in each monomial term. -/
theorem exists_quadratic_expansion {R : Type*} [CommSemiring R] (l n d : ℕ)
    (P : MvPolynomial (Fin l ⊕ Fin n) R)
    (hdeg : ∀ s : (Fin l ⊕ Fin n) →₀ ℕ, MvPolynomial.coeff s P ≠ 0 →
      (∑ i : Fin l, s (Sum.inl i)) ≤ d ∧ (∑ j : Fin n, s (Sum.inr j)) ≤ 2) :
    ∃ C : (Fin (n + 1) × Fin (n + 1)) → (Fin d → Fin (l + 1)) → R,
      ∀ (x : Fin l → R) (y : Fin n → R),
        MvPolynomial.eval (Sum.elim x y) P =
          ∑ ij : Fin (n + 1) × Fin (n + 1), ∑ tau : Fin d → Fin (l + 1),
            C ij tau * (∏ i : Fin d, Fin.snoc (α := fun _ => R) x 1 (tau i)) *
              Fin.snoc (α := fun _ => R) y 1 ij.1 * Fin.snoc (α := fun _ => R) y 1 ij.2 :=
  by
    classical
    choose publicTuple hpub using fun s : P.support =>
      exists_padded_tuple (R := R) l d (fun i => s.val (Sum.inl i))
        (hdeg s.val (MvPolynomial.mem_support_iff.mp s.property)).1
    choose privateTuple hpriv using fun s : P.support =>
      exists_padded_tuple (R := R) n 2 (fun i => s.val (Sum.inr i))
        (hdeg s.val (MvPolynomial.mem_support_iff.mp s.property)).2
    let privatePair (s : P.support) : Fin (n + 1) × Fin (n + 1) :=
      (privateTuple s 0, privateTuple s 1)
    let C : (Fin (n + 1) × Fin (n + 1)) → (Fin d → Fin (l + 1)) → R :=
      fun ij tau => ∑ s : P.support,
        if privatePair s = ij ∧ publicTuple s = tau then P.coeff s.val else 0
    refine ⟨C, fun x y => ?_⟩
    have hEval : MvPolynomial.eval (Sum.elim x y) P =
        ∑ s : P.support, P.coeff s.val *
          (∏ i : Fin d, Fin.snoc (α := fun _ => R) x 1 (publicTuple s i)) *
          Fin.snoc (α := fun _ => R) y 1 (privatePair s).1 *
          Fin.snoc (α := fun _ => R) y 1 (privatePair s).2 := ?_
    swap
    · rw [MvPolynomial.eval_eq', ← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← hpub s x, ← hpriv s y, Fin.prod_univ_two]
      simp only [privatePair, mul_assoc]
    rw [hEval]
    symm
    simp only [C, Finset.sum_mul]
    simp_rw [Finset.sum_comm
      (s := (Finset.univ : Finset (Fin d → Fin (l + 1))))
      (t := (Finset.univ : Finset P.support))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq]
