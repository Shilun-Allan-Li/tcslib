/-- A source-group matrix word contains exactly one public-width block for each entry,
including empty row or column sets. This transports the existing pairing serialization law.

**Proof sketch.** Read groupMatrix_eq, groupVector_eq and groupMatrixEnc_eq to identify
the words. Reuse BilinearGroup.length_groupMatrixEnc; do not recount flatten lengths. -/
theorem groupMatrix_length {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) pp.group.G) :
    (groupMatrix pp A).length = m * n * G.wG.eval κ := by
  simpa only [groupMatrix_eq, groupVector_eq, BilinearGroup.groupMatrixEnc_eq] using
    (pp.group.length_groupMatrixEnc A)
