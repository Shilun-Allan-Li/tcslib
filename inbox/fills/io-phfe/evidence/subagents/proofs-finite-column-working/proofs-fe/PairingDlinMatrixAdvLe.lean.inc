/-- Canonical DLIN bounds the matrix DLIN advantage with the explicit diagonal-zero slack
[GJLS21, Definition 3.3, p. 18; JLS26, §1.1, p. 3].

**Proof sketch.** Apply the triangle inequality to the random acceptance probabilities,
using `dlinMatrixGame_real_accept` and `dlinMatrixGame_random_gap_le`. -/
theorem dlinMatrixAdv_le (D : NUPPT) (κ : ℕ) :
    G.dlinMatrixAdv D κ ≤ G.dlinAdv D κ + G.dlinMatrixSlack κ := by
  rw [dlinMatrixAdv_eq, dlinAdv_eq, advantage_eq, advantage_eq,
    dlinMatrixGame_real_accept]
  calc
    |accept (G.dlinMatrixGame D false κ) - accept (G.dlinGame D true κ)| ≤
        |accept (G.dlinMatrixGame D false κ) - accept (G.dlinGame D false κ)| +
          |accept (G.dlinGame D false κ) - accept (G.dlinGame D true κ)| :=
      abs_sub_le _ _ _
    _ ≤ G.dlinMatrixSlack κ +
        |accept (G.dlinGame D false κ) - accept (G.dlinGame D true κ)| :=
      add_le_add_right (G.dlinMatrixGame_random_gap_le D κ) _
    _ = |accept (G.dlinGame D false κ) - accept (G.dlinGame D true κ)| +
        G.dlinMatrixSlack κ := add_comm _ _
