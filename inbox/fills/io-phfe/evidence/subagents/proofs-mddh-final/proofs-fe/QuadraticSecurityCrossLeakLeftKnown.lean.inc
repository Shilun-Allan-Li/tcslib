/-- Left mixed leakage equals the scalar tensor leakage whenever the supplied group
vector is the encoding of a KNOWN scalar vector [Wee20, §3.3, pp. 7–8].

**Proof sketch.** Read crossLeakLeft_eq and value_eq. Reuse the groupDot and exponent
multiplication transport laws and the canonical privateTensor coordinate reader. The
scalar y1 is supplied as a theorem parameter; no algorithm computes it from group y1. -/
theorem crossLeakLeft_known (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (y2 : Fin (n2.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    crossLeakLeft G n1 n2 PG κ pp f x (pp.group.expVec pp.generator y1) y2 mu =
      pp.generator ^ (value G n1 n2 PG κ pp f x y1 y2).val * mu⁻¹ := by
  have hTensor :
      (fun i : Fin (n1.eval κ * n2.eval κ) =>
        pp.group.expVec pp.generator y1 (finProdFinEquiv.symm i).1 ^
          (y2 (finProdFinEquiv.symm i).2).val) =
        pp.group.expVec pp.generator (privateTensor (p := pp.orderParam) y1 y2) := ?_
  swap
  · funext i
    have h := congrFun (pp.group.expVec_tensor_left pp.generator y1 y2)
      (finProdFinEquiv.symm i)
    simpa only [pp.group.expVec_apply, privateTensor_eq, Matrix.kroneckerMap_apply] using h
  rw [crossLeakLeft_eq, hTensor, pp.group.groupDot_expVec, value_eq]
