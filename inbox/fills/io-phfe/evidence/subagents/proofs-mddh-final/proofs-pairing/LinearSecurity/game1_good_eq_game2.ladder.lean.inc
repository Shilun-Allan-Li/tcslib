/-- The basis decomposition changes no good-event transcript
[Wee20, Appendix B, Game 2, p. 13].

**Proof sketch.** On nonzero determinant, use the total inverse's published left/right
inverse laws and group matrix-action identities to reconstruct each honest key. Couple
all adaptive queries with `expect_simulate_rel`; both filtered games return false on bad H. -/
theorem game1_good_eq_game2 (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (κ : ℕ) (pp : PublicParams G κ) (ω : SecurityDraw G PG zDim A.budget κ pp)
    (r : List Bool) :
    (if (basisMatrix G κ pp
          (setupAt G PG zDim A.budget κ pp ω).1
          (setupAt G PG zDim A.budget κ pp ω).2.1).det = 0 then false
      else runGameDet G PG zDim A 1 false κ pp ω r) =
      runGameDet G PG zDim A 2 true κ pp ω r := by
  classical
  letI : Fact (Nat.Prime pp.group.order) := ⟨pp.group.order_prime⟩
  let θ := setupAt G PG zDim A.budget κ pp ω
  let ctx := simSetupCore G ℓ zDim κ pp θ
  let H := basisMatrix G κ pp θ.1 θ.2.1
  have hRank : (basisMatrix G κ pp ctx.2.A ctx.2.c).det = H.det := ?_
  swap
  · simp only [ctx, H, simSetupCore_eq]
  have hInv : ctx.2.basisInv = H⁻¹ := ?_
  swap
  · simp only [ctx, H, simSetupCore_eq]
  have hr1 : runGameDet G PG zDim A 1 false κ pp ω r =
      (runDet (A.next κ pp ctx.1 r) false
        (gameHandler G PG zDim A.budget 1 κ pp ctx.2 ω)
        (A.budget.eval κ) [] ⟨none, 0⟩).1 := ?_
  swap
  · simpa [ctx, θ, simSetupCore_eq] using
      (runGameDet_eq G PG zDim A 1 false κ pp ω r)
  have hr2 : runGameDet G PG zDim A 2 true κ pp ω r =
      if H.det = 0 then false else
        (runDet (A.next κ pp ctx.1 r) false
          (gameHandler G PG zDim A.budget 2 κ pp ctx.2 ω)
          (A.budget.eval κ) [] ⟨none, 0⟩).1 := ?_
  swap
  · simpa [ctx, θ, H, simSetupCore_eq] using
      (runGameDet_eq G PG zDim A 2 true κ pp ω r)
  change (if H.det = 0 then false else runGameDet G PG zDim A 1 false κ pp ω r) = _
  rw [hr1, hr2]
  by_cases hbad : H.det = 0
  · simp only [if_pos hbad]
  · simp only [if_neg hbad]
    have hUnit : IsUnit H.det := isUnit_iff_ne_zero.mpr hbad
    have hInvMul : ctx.2.basisInv * H = 1 := ?_
    swap
    · rw [hInv]
      exact Matrix.nonsing_inv_mul H hUnit
    have hReconstruct : ∀ {J : Type} (K : Matrix (Fin 3) J pp.group.G),
        combineRows G κ pp
          (fun i j => ctx.2.basisInv i (Fin.castSucc j))
          (fun i => ctx.2.basisInv i (Fin.last 2))
          (matMulGroup ctx.2.Aᵀ K) (groupVecMul ctx.2.c K) = K := ?_
    swap
    · intro J K
      -- Remaining local algebra: recombine the two-plus-one rows, then use hInvMul.
      -- Reuse combineRows_eq, basisMatrix_eq, Fin.prod_univ_castSucc,
      -- pp.group.groupVecMul_matMulGroup and scalar matrix product/identity readers.
      sorry
    have hKey : ∀ (query : KeyQuery G PG zDim κ pp)
        (kr : KeyDraw G PG κ pp query.fn),
        decomposedKey G PG zDim κ pp ctx.2 query kr =
          keyCore G PG zDim κ pp ⟨ctx.2.W, ctx.2.U, ctx.2.V⟩ query.fn query.matrix kr := ?_
    swap
    · intro query kr
      rw [decomposedKey_eq]
      simp only [hReconstruct]
      rfl
    have hHandlers : gameHandler G PG zDim A.budget 1 κ pp ctx.2 ω =
        gameHandler G PG zDim A.budget 2 κ pp ctx.2 ω := ?_
    swap
    · simp [gameHandler_eq, hKey]
    rw [hHandlers]
