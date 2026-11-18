/-- The second decryption block is the second partial-garbling block at coins `sAT`
[Wee20, §4.2, p. 10, (10)].

**Proof sketch.** Use the known-scalar matrix and pairing transport laws. The mixed-product
identity `(I⊗R)(x⊗I)=(x⊗I)R` identifies the two `U` terms. Cancel them and the two `V`
terms; the remaining matrix expression is `(sAT)(L1(x⊗I)+L0)`. -/
theorem decSecond_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    decSecond G PG zDim κ pp f x
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      pp.group.expVecT (pp.group.pair pp.generator pp.generator)
        (Matrix.vecMul (Matrix.vecMul (Matrix.vecMul s a.1) t.1)
          ((show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
              (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
                pp.orderParam)
                (M := PG.MIdx κ pp.orderParam f) x) + (show Matrix _ _ (ZMod pp.group.order) from
                  PG.L0 κ pp.orderParam f))) :=
  by
    let X := PartialGarbling.publicTensor (p := pp.orderParam)
      (M := PG.MIdx κ pp.orderParam f) x
    let X2 := PartialGarbling.publicTensor (p := pp.orderParam) (M := Fin 2) x
    let T := t.1
    let R := t.2
    let U := a.2.2.1
    let V := a.2.2.2
    let H := Matrix.kroneckerMap (fun c r => c * r)
      (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
    let L1m := (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f)
    let L0m := (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)
    let sa := Matrix.vecMul s a.1
    let value := Matrix.vecMul (Matrix.vecMul sa T) (L1m * X + L0m)
    let mask := Matrix.vecMul (Matrix.vecMul sa (U * X2 + V)) R
    let sk := keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t
    let ct := encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
      (pp.group.expVec pp.generator z) s
    let K := groupMatMul sk.K2 X
    have hMix : H * X = X2 * R := sorry
    have hMatrix : (T * L1m + U * H) * X + (T * L0m + V * R) =
        T * (L1m * X + L0m) + (U * X2 + V) * R := ?_
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hMix,
        add_assoc, add_comm, add_left_comm]
    have hNumerator (m : PG.MIdx κ pp.orderParam f) :
        pp.group.pairVec ct.c0 (fun i => K i m * sk.K3 i m) =
          pp.group.pair pp.generator pp.generator ^ (value m).val *
            pp.group.pair pp.generator pp.generator ^ (mask m).val := sorry
    have hDenominator (m : PG.MIdx κ pp.orderParam f) :
        pp.group.pairVec ct.c2 (fun i => sk.R i m) =
          pp.group.pair pp.generator pp.generator ^ (mask m).val := sorry
    change decSecond G PG zDim κ pp f x sk ct =
      pp.group.expVecT (pp.group.pair pp.generator pp.generator) value
    rw [decSecond_eq]
    funext m
    rw [hNumerator m, hDenominator m, pp.group.expVecT_apply, mul_inv_cancel_right]
