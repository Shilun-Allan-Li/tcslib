theorem groupVector_injective {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {n : ℕ} :
    Function.Injective (groupVector pp (n := n))  := by
  intro v w h
  have hrow :
      pp.group.groupMatrixEnc (fun (_ : Fin 1) (j : Fin n) => v j) =
        pp.group.groupMatrixEnc (fun (_ : Fin 1) (j : Fin n) => w j) := ?_
  swap
  · simpa only [groupVector_eq, BilinearGroup.groupMatrixEnc_eq, List.ofFn_const,
      List.replicate_one, List.flatten_singleton] using h
  exact congrArg (fun M : Matrix (Fin 1) (Fin n) pp.group.G => M 0)
    (pp.group.groupMatrixEnc_injective hrow)
