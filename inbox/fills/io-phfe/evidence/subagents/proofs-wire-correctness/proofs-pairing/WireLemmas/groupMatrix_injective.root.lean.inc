theorem groupMatrix_injective {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {m n : ℕ} :
    Function.Injective (groupMatrix pp (m := m) (n := n))  := by
  intro A B h
  apply pp.group.groupMatrixEnc_injective
  simpa only [groupMatrix_eq, groupVector_eq, BilinearGroup.groupMatrixEnc_eq] using h
