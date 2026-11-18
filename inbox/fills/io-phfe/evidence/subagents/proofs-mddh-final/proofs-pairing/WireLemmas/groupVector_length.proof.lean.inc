/-- A source-group vector word contains exactly one public-width block per coordinate,
including the empty vector. It is the one-row case of the existing matrix serialization.

**Proof sketch.** Regard the vector as a one-row matrix. Use groupVector_eq and the
pairing encoder's equation reader plus existing singleton-list equations, then reuse
BilinearGroup.length_groupMatrixEnc at one row. -/
theorem groupVector_length {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {n : ℕ}
    (v : Fin n → pp.group.G) :
    (groupVector pp v).length = n * G.wG.eval κ := by
  simpa only [groupVector_eq, BilinearGroup.groupMatrixEnc_eq, List.ofFn_const,
    List.replicate_one, List.flatten_singleton, Nat.one_mul] using
    (pp.group.length_groupMatrixEnc (fun (_ : Fin 1) (j : Fin n) => v j))
