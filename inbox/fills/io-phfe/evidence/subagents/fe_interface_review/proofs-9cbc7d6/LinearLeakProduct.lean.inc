/-- The leakage is the product of the supplied group-matrix entries raised to the known
coefficients `z_a f_b(x)` [Wee20, §4, p. 8].

**Proof sketch.** Read `leak_eq`, `groupMulVec_apply` and `groupDot_eq`. Distribute powers
across finite products, use the source-group modular multiplication law, and commute the
two known scalar factors. No exponent of a group element is recovered. -/
theorem leak_product (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order) :
    leak G PG zDim κ pp f M x z =
      ∏ a, ∏ b, M a b ^ (z a * (show ZMod pp.group.order from PG.eval κ pp.orderParam f x b)).val :=
  by
    rw [leak_eq, groupDot_eq]
    apply Finset.prod_congr rfl
    intro a _
    rw [groupMulVec_apply, groupDot_eq, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro b _
    rw [← pow_mul, ← pp.group.pow_val_mul,
      mul_comm (PG.eval κ pp.orderParam f x b) (z a)]
