/-- The allowed class value is the quadratic scheme's scalar value on the duplicated
private input [GJLS21, Section 9; Wee20, Section 3.1].

**Proof sketch.** Read the published class evaluation and parameter/value codec equations.
Transport the three input widths through the supplied equality readers. Substitute the
supplied garbling's semantic agreement and use the diagonal class embedding identity. -/
theorem PHFE.class_eval_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (hPG : PHFE.PGSound PG)
    (κ : ℕ) (pp : PublicParams G κ)
    (f : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (y : Fin ((phfeClass ℓ n G.wG d).privLen.eval κ) → Bool) :
    PHFE.valueEquiv G ℓ n d κ pp
        ((phfeClass ℓ n G.wG d).eval κ (PHFE.classParam G ℓ n d κ pp) f x y) =
      Quadratic.value G n n PG κ pp (PHFE.decodeFunction G ℓ n d κ pp f)
        (PHFE.decodePublic G ℓ n d κ pp x)
        (PHFE.decodePrivate G ℓ n d κ pp y) (PHFE.decodePrivate G ℓ n d κ pp y) := by
  rw [Quadratic.value_eq, (PHFE.pgSound_iff PG).mp hPG]
  simp only [PHFE.valueEquiv_eq, phfeClassValueEquiv_eq, PHFE.classParam_eq,
    phfeClassParamEquiv_eq, Equiv.refl_symm, Equiv.refl_apply,
    phfeClass_eval, phfeEval_eq, quadEval_eq, PHFE.decodeFunction_eq,
    PHFE.decodePublic_eq, PHFE.decodePrivate_eq, finCongr_refl,
    Equiv.coe_refl, Function.comp_id]
  rfl
