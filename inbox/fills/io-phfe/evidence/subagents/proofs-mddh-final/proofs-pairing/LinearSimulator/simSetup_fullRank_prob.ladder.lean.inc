/-- The good basis event has exactly the general-linear-group fraction, with no conditioning
on the first two columns [Wee20, §4.2, p. 10, Setup*, exact reading of its draw].

**Proof sketch.** Reindex the independent `A,c` coordinates as a uniform three-by-three
matrix. Integrate unused masks. Count invertible matrices with `Matrix.card_GL_field` and
divide by the cardinality of all matrices, using `ZMod.card`. -/
theorem simSetup_fullRank_prob (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) :
    ProbComp.prob (ProbComp.sample (SimSetupDraw G ℓ zDim κ pp))
      (fun ω => IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) = 1 - rankSlack pp := by
  classical
  let K := ZMod pp.group.order
  let Tail : Type :=
    Matrix (Fin 3) (Fin (zDim.eval κ)) K ×
      Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) K ×
      Matrix (Fin 3) (Fin 2) K ×
      (Fin (zDim.eval κ) → K) × (Fin 2 → K)
  let row : ((Fin 2 → K) × K) ≃ (Fin 3 → K) :=
    (Equiv.prodComm (Fin 2 → K) K).trans
      (Fin.snocEquiv (fun _ : Fin 3 => K))
  let ac : (Matrix (Fin 3) (Fin 2) K × (Fin 3 → K)) ≃
      Matrix (Fin 3) (Fin 3) K :=
    (Equiv.arrowProdEquivProdArrow (Fin 3)
      (fun _ => Fin 2 → K) (fun _ => K)).symm.trans
      ((Equiv.piCongrRight (fun _ : Fin 3 => row)).trans
        (Equiv.piComm (fun (_ : Fin 3) (_ : Fin 3) => K)))
  let e : SimSetupDraw G ℓ zDim κ pp ≃ (Matrix (Fin 3) (Fin 3) K × Tail) :=
    (Equiv.prodAssoc (Matrix (Fin 3) (Fin 2) K) (Fin 3 → K) Tail).symm.trans
      (Equiv.prodCongr ac (Equiv.refl Tail))
  have hBasis : ∀ ω : SimSetupDraw G ℓ zDim κ pp,
      (e ω).1 = basisMatrix G κ pp ω.1 ω.2.1 := sorry
  have hEvent :
      (fun ω : SimSetupDraw G ℓ zDim κ pp =>
        IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) =
      (fun ω : SimSetupDraw G ℓ zDim κ pp => IsUnit (e ω).1) := ?_
  swap
  · funext ω
    rw [hBasis ω]
    exact propext (Matrix.isUnit_iff_isUnit_det _).symm
  have hDist :
      ProbComp.prob (ProbComp.sample (SimSetupDraw G ℓ zDim κ pp))
          (fun ω => IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) =
        ProbComp.prob (ProbComp.sample (Matrix (Fin 3) (Fin 3) K))
          (fun M => IsUnit M) := ?_
  swap
  · rw [Bridge.prob_sample_eq_uprob, Bridge.prob_sample_eq_uprob, hEvent]
    exact (uprob_comp_equiv e
      (fun z : Matrix (Fin 3) (Fin 3) K × Tail => IsUnit z.1)).trans
        (uprob_fst (β := Tail) (fun M : Matrix (Fin 3) (Fin 3) K => IsUnit M))
  have hCount :
      (((∏ i : Fin 3,
          (Fintype.card K ^ 3 - Fintype.card K ^ (i : ℕ))) : ℕ) : ℝ) /
          (Fintype.card K : ℝ) ^ (3 * 3) =
        (1 - 1 / (pp.group.order : ℝ)) *
          (1 - 1 / (pp.group.order : ℝ) ^ 2) *
          (1 - 1 / (pp.group.order : ℝ) ^ 3) := sorry
  calc
    _ = ProbComp.prob (ProbComp.sample (Matrix (Fin 3) (Fin 3) K))
        (fun M => IsUnit M) := hDist
    _ = _ := prob_sample_matrix_isUnit_eq (K := K) 3
    _ = _ := hCount
    _ = 1 - rankSlack pp := ?_
  rw [rankSlack_eq]
  ring
