/-- Uniform scalar responses and responses multiplied by two independent diagonal masks
have expectation gap at most `2/N - 1/N²` for every test with values in `[0,1]`, where `N`
is the finite field's cardinality. This is fixed-field probability glue for the random-law
comparison [GJLS21, Definition 3.3, p.18; JLS26, §1.1, p.3].

**Proof sketch.** Fix the diagonal pair. If both entries are nonzero, their coordinatewise
multiplication permutations preserve the uniform response law. Otherwise each bounded
expectation lies in `[0,1]`, so its gap is at most one. Average the resulting bad-event
indicator with `abs_expect_sub_le_expect`. Reindex the two diagonal coordinates as a product
and evaluate the exact bad mass `1/N + (1-1/N)/N = 2/N - 1/N²`, using existing singleton
probability and sample/Fubini readers. No sampler is constructed. -/
theorem dlinDiagonal_random_gap_le {K : Type} [Field K] [Fintype K]
    (H : (Fin 2 → K) → (Fin 3 → K) → ℝ)
    (hH0 : ∀ ab u, 0 ≤ H ab u) (hH1 : ∀ ab u, H ab u ≤ 1) :
    |ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 3 → K)) (H ab)) -
      ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K)
            (fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t])))| ≤
      2 / (Fintype.card K : ℝ) - 1 / (Fintype.card K : ℝ) ^ 2 := by
  classical
  let A : (Fin 2 → K) → ℝ := fun ab =>
    ProbComp.expect (ProbComp.sample (Fin 3 → K)) (H ab)
  let B : (Fin 2 → K) → ℝ := fun ab =>
    ProbComp.expect (ProbComp.sample (Fin 2 → K)) fun rs =>
      ProbComp.expect (ProbComp.sample K) fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t]
  let bad : (Fin 2 → K) → Prop := fun ab => ab 0 = 0 ∨ ab 1 = 0
  have hA0 (ab : Fin 2 → K) : 0 ≤ A ab := ProbComp.expect_nonneg _ (hH0 ab)
  have hA1 (ab : Fin 2 → K) : A ab ≤ 1 :=
    calc
      A ab ≤ ProbComp.expect (ProbComp.sample (Fin 3 → K)) (fun _ => 1) :=
        ProbComp.expect_mono _ (hH1 ab)
      _ = 1 := ProbComp.expect_const _ 1
  have hB0 (ab : Fin 2 → K) : 0 ≤ B ab :=
    ProbComp.expect_nonneg _ (fun rs => ProbComp.expect_nonneg _
      (fun t => hH0 ab ![ab 0 * rs 0, ab 1 * rs 1, t]))
  have hB1 (ab : Fin 2 → K) : B ab ≤ 1 :=
    calc
      B ab ≤ ProbComp.expect (ProbComp.sample (Fin 2 → K)) (fun _ => 1) :=
        ProbComp.expect_mono _ (fun rs =>
          calc
            ProbComp.expect (ProbComp.sample K)
                (fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t]) ≤
              ProbComp.expect (ProbComp.sample K) (fun _ => 1) :=
              ProbComp.expect_mono _ (fun t => hH1 ab ![ab 0 * rs 0, ab 1 * rs 1, t])
            _ = 1 := ProbComp.expect_const _ 1)
      _ = 1 := ProbComp.expect_const _ 1
  have hGood : ∀ ab : Fin 2 → K, ab 0 ≠ 0 → ab 1 ≠ 0 → A ab = B ab := sorry
  have hBadMass :
      ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun ab => if bad ab then (1 : ℝ) else 0) =
        2 / (Fintype.card K : ℝ) - 1 / (Fintype.card K : ℝ) ^ 2 := sorry
  have hPoint : ∀ ab : Fin 2 → K,
      |A ab - B ab| ≤ if bad ab then (1 : ℝ) else 0 := ?_
  · intro ab
    by_cases hb : bad ab
    · rw [if_pos hb, abs_le]
      constructor <;> linarith [hA0 ab, hA1 ab, hB0 ab, hB1 ab]
    · have ha0 : ab 0 ≠ 0 := fun h => hb (Or.inl h)
      have ha1 : ab 1 ≠ 0 := fun h => hb (Or.inr h)
      simpa only [if_neg hb, hGood ab ha0 ha1, sub_self, abs_zero] using
        (le_refl (0 : ℝ))
  have hAverage := ProbComp.abs_expect_sub_le_expect
    (ProbComp.sample (Fin 2 → K)) hPoint
  rw [hBadMass] at hAverage
  exact hAverage
