/-- With known scalar allowed value, the simulated cross term represents the corresponding
scalar difference [Wee20, §3.3, p. 7, Game 2 and (5)].

**Proof sketch.** Read `crossLeak_eq`, then use the published source-group additive and
negation exponent laws. This uses a supplied scalar value, not an exponent extracted from mu. -/
theorem crossLeak_known_value (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (mu : ZMod pp.group.order) :
    crossLeak G n1 n2 PG κ pp st f x (pp.generator ^ mu.val) =
      pp.generator ^ (value G n1 n2 PG κ pp f x st.y1 st.y2 - mu).val := by
  simp only [crossLeak_eq, value_eq, sub_eq_add_neg,
    pp.group.pow_val_add, pp.group.pow_val_neg]
