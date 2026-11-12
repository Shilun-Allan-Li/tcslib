/- Fixture for scripts/copy-text-screen-v4.py (not part of the library build): a theorem followed
by an anonymous `example` with the same statement and body. The screen should report the pair
between the two; v3 read the example as part of the theorem's body and reported nothing. -/
namespace Fixture

theorem sum_range_id_mul_two (n : ℕ) :
    (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, add_mul, ih]; cases k <;> simp; ring

example (n : ℕ) :
    (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, add_mul, ih]; cases k <;> simp; ring

end Fixture
