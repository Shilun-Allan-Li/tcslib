/- Fixture for scripts/copy-text-screen-v4.py, shaped like quantum E1 `Measure.lean` at a97fceca:
an unrelated theorem, then an `example`, then the theorem the example duplicates. v3 attributed
the copy to the unrelated theorem (whose body absorbed the example); v4 pairs the example with
its twin. -/
namespace Fixture

theorem length_append_reverse (l m : List ℕ) :
    (l ++ m.reverse).length = m.length + l.length := by
  rw [List.length_append, List.length_reverse, Nat.add_comm]
example (l : List ℕ) (a : ℕ) :
    (a :: l).reverse.length = l.length + 1 := by
  rw [List.length_reverse, List.length_cons]
  simp only [Nat.add_comm, Nat.add_left_cancel_iff, List.length_reverse]

/-- The twin. -/
theorem length_reverse_cons (l : List ℕ) (a : ℕ) :
    (a :: l).reverse.length = l.length + 1 := by
  rw [List.length_reverse, List.length_cons]
  simp only [Nat.add_comm, Nat.add_left_cancel_iff, List.length_reverse]

theorem zero_le_length (l : List ℕ) : 0 ≤ l.length := Nat.zero_le _

end Fixture
