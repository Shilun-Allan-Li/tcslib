/-- A surjective scalar column map sends a uniform coefficient matrix to a uniform output
matrix. This is finite-field distribution glue; no sampler or machine is constructed.

**Proof sketch.** Regard the matrix product as independent applications of the surjective
linear map to each column. All fibers are translates of its kernel and have equal size;
reuse the finite linear quotient/fiber and uniform-average APIs. -/
theorem expect_sample_matrix_mul_of_mulVec_surjective
    {K : Type} [Field K] [Fintype K] {r m c : ℕ}
    (M : Matrix (Fin r) (Fin m) K) (hM : Function.Surjective (Matrix.mulVec M))
    (F : Matrix (Fin r) (Fin c) K → ℝ) :
    ProbComp.expect (ProbComp.sample (Matrix (Fin m) (Fin c) K)) (fun S => F (M * S)) =
      ProbComp.expect (ProbComp.sample (Matrix (Fin r) (Fin c) K)) F := by
  classical
  obtain ⟨R, hR⟩ :=
    (Matrix.mulVec_surjective_iff_exists_right_inverse (A := M)).mp hM
  let f : Matrix (Fin m) (Fin c) K →+ Matrix (Fin r) (Fin c) K :=
    Matrix.addMonoidHomMulLeft M
  have hf : Function.Surjective f := ?_
  swap
  · intro U
    refine ⟨R * U, ?_⟩
    change M * (R * U) = U
    rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  let e : Matrix (Fin m) (Fin c) K ≃ (Matrix (Fin r) (Fin c) K × f.ker) :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      (Equiv.sigmaEquivProdOfEquiv
        (fun U => AddMonoidHom.fiberEquivKerOfSurjective (f := f) hf U))
  have hFst (S : Matrix (Fin m) (Fin c) K) : (e S).1 = M * S := rfl
  have h := ProbComp.expect_sample_equiv e (fun p => F p.1)
  simp only [hFst] at h
  rw [h, ← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, ProbComp.expect_const]
