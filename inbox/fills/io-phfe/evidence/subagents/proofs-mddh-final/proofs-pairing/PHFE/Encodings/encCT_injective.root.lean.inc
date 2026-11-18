theorem encCT_injective (G : BilinearGen) (n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : Function.Injective (encCT G n κ pp)  := by
  intro c d h
  have hw := congrArg List.ofFn h
  simp only [encCT_eq] at hw
  rw [ofFn_padFin_of_length (quadraticCT_length G n κ pp c),
    ofFn_padFin_of_length (quadraticCT_length G n κ pp d)] at hw
  simp only [Wire.quadraticCT_eq, Wire.linearCT_eq, List.append_assoc] at hw
  rcases c with ⟨y1, y2, ⟨c0, c1, c2⟩⟩
  rcases d with ⟨z1, z2, ⟨d0, d1, d2⟩⟩
  rcases List.append_inj hw (by simp only [Wire.groupVector_length]) with ⟨h1, ht⟩
  rcases List.append_inj ht (by simp only [Wire.groupVector_length]) with ⟨h2, hl⟩
  rcases List.append_inj hl (by simp only [Wire.groupVector_length]) with ⟨h0, hl⟩
  rcases List.append_inj hl (by simp only [Wire.groupVector_length]) with ⟨hc1, hc2⟩
  cases Wire.groupVector_injective pp h1
  cases Wire.groupVector_injective pp h2
  cases Wire.groupVector_injective pp h0
  cases Wire.groupVector_injective pp hc1
  cases Wire.groupVector_injective pp hc2
  rfl
