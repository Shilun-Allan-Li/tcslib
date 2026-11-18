/-- A parameterized translation by a kernel-valued function of a public projection is
an equivalence. It fixes the latent parameter and that projection, and its inverse
subtracts the same shift. This is a logical algebra lemma, not a runtime interface. -/
theorem exists_fiberwise_add_right_equiv {U E P : Type*} [AddGroup E] [AddGroup P]
    (projection : E →+ P) (shift : U → P → E)
    (hshift : ∀ (u : U) (p : P), projection (shift u p) = 0) :
    ∃ e : (U × E) ≃ (U × E),
      (∀ (u : U) (x : E), e (u, x) = (u, x + shift u (projection x))) ∧
      (∀ (u : U) (x : E), e.symm (u, x) = (u, x - shift u (projection x))) ∧
      (∀ (u : U) (x : E), projection (e (u, x)).2 = projection x) := by
  have hpres : ∀ (u : U) (p : P) (x : E),
      projection x = p ↔ projection (Equiv.addRight (shift u p) x) = p := ?_
  swap
  · intro u p x
    simp only [Equiv.coe_addRight, map_add, hshift, add_zero]
  let fiber : ∀ (u : U) (p : P),
      {x : E // projection x = p} ≃ {x : E // projection x = p} :=
    fun u p => (Equiv.addRight (shift u p)).subtypeEquiv (hpres u p)
  let e : (U × E) ≃ (U × E) :=
    Equiv.prodCongrRight (fun u => Equiv.ofFiberEquiv (fiber u))
  have hf : ∀ (u : U) (x : E),
      e (u, x) = (u, x + shift u (projection x)) := ?_
  swap
  · intro u x
    simp only [e, Equiv.prodCongrRight_apply, Equiv.ofFiberEquiv_apply,
      fiber, Equiv.subtypeEquiv_apply, Equiv.coe_addRight]
  refine ⟨e, hf, ?_, ?_⟩
  · intro u x
    apply (Equiv.symm_apply_eq e).mpr
    rw [hf]
    simp only [map_sub, hshift, sub_zero, sub_add_cancel]
  · intro u x
    simpa only [e, Equiv.prodCongrRight_apply] using
      (Equiv.ofFiberEquiv_map (fiber u) x)
