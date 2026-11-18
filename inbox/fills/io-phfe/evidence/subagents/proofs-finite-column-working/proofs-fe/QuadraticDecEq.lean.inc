/-- The raw quadratic scheme decrypts perfectly to the allowed value in the target group
for every honest setup, encryption and key draw [Wee20, §3.1, p. 6, (4)–(5)].

**Proof sketch.** Read the cores and use `expVec_vecMul` to identify the known scalar
masked vectors from the setup draw. Apply `mixGroup_exp` and `signalGroup_exp`, then Π's
`pi_dec_eq`. Use `cross_value_identity` to cancel Π's result from the paired tensor term.
Finish with the target-group additive and negation exponent laws. -/
theorem quadratic_dec_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ n1 n2 κ pp) (s : EncDraw G κ pp)
    (t : Linear.KeyDraw G PG κ pp f) :
    dec G n1 n2 PG κ pp f x
        (keyCore G n1 n2 PG κ pp (setupCore G ℓ n1 n2 κ pp a).2 f t)
        (encCore G ℓ n1 n2 κ pp (setupCore G ℓ n1 n2 κ pp a).1 x z1 z2 s) =
      pp.group.pair pp.generator pp.generator ^ (value G n1 n2 PG κ pp f x z1 z2).val := by
  let y1 := Matrix.vecMul s.1 a.1 + z1
  let y2 := Matrix.vecMul s.2.1 a.2.1 + z2
  let signal := signalScalar (p := pp.orderParam) s.1 z2 y1 s.2.1
  let F := mixScalar (p := pp.orderParam) a.1 a.2.1
  let fx := PG.eval κ pp.orderParam f x
  let egg := pp.group.pair pp.generator pp.generator
  have hTensor :
      (fun i => pp.group.pairTensor (pp.group.expVec pp.generator y1)
        (pp.group.expVec pp.generator y2) (finProdFinEquiv.symm i)) =
      pp.group.expVecT egg (privateTensor (p := pp.orderParam) y1 y2) := ?_
  swap
  · rw [pp.group.pairTensor_expVec]
    funext i
    simp only [pp.group.expVecT_apply, privateTensor_eq, Matrix.kroneckerMap_apply]
    rfl
  have hLeak :
      pp.group.pair pp.generator
          (Linear.leak G PG (piDim n1 n2) κ pp f
            (pp.group.expMat pp.generator F) x signal) =
        egg ^ (dotProduct signal (F *ᵥ fx)).val := ?_
  swap
  · rw [Linear.leak_eq, pp.group.expMat_mulVec, pp.group.groupDot_expVec,
      dotProduct_comm, pp.group.pair_pow_right]
  have hValue : dotProduct (privateTensor (p := pp.orderParam) z1 z2) fx =
      dotProduct (privateTensor (p := pp.orderParam) y1 y2) fx -
        dotProduct signal (F *ᵥ fx) :=
    cross_value_identity (p := pp.orderParam) a.1 a.2.1 s.1 s.2.1 z1 z2 fx
  simp only [dec_eq, keyCore_eq, encCore_eq, setupCore_eq,
    pp.group.expVec_vecMul, ← pp.group.expVec_add, mixGroup_exp, signalGroup_exp]
  rw [Linear.pi_dec_eq, hTensor, pp.group.groupDot_expVecT, hLeak, value_eq,
    hValue, sub_eq_add_neg, pp.group.pow_val_add_GT, pp.group.pow_val_neg_GT]
