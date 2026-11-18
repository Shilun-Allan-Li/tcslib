/-- Every advice family has the same polynomial length bound. Technical glue.

**Proof sketch.** Use `length_pairEncode`, `Candidates.length_natToList`, the unary and
one-hot lengths, and `Encoding.Modular.encodeMatrix_length`. Bound each binary dimension
length by its value plus one and use the polynomial evaluation readers. -/
theorem length_mddhAdviceEnc_le (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (κ : ℕ) (ω : MddhAdvice p d ℓ κ) :
    (G.mddhAdviceEnc p hp d ℓ κ ω).length ≤ (G.mddhAdviceLen d ℓ).eval κ := by
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  have hd := Turing.length_bits_le_self (d.eval κ)
  have hℓ := Turing.length_bits_le_self (ℓ.eval κ)
  rw [Nat.size_eq_bits_len] at hd hℓ
  rw [G.mddhAdviceEnc_eq p hp d ℓ κ ω, G.mddhAdviceLen_eq d ℓ]
  simp only [length_pairEncode, List.length_replicate, Candidates.length_natToList,
    List.length_append, List.length_ofFn, Encoding.Modular.encodeMatrix_length,
    PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var, PolyExpr.eval_const,
    Nat.add_mul]
  omega
