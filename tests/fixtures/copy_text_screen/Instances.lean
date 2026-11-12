/- Fixture for scripts/copy-text-screen-v4.py: two anonymous instances with the same body (one
after `:`, one after a binder), a short anonymous `example` that is not screened but still advances
the `<example #k>` count, a screened `example`, and a named prioritized instance. -/
namespace Fixture

structure Box (n : ℕ) where
  val : Fin (n + 1)

example : (0 : ℕ) = 0 := rfl

instance : Inhabited (Box 0) where
  default := { val := ⟨0, Nat.zero_lt_succ 0⟩ } |> fun b => { b with val := ⟨0, Nat.zero_lt_succ 0⟩ }

instance (w : ℕ) : Inhabited (Box w) where
  default := { val := ⟨0, Nat.zero_lt_succ w⟩ } |> fun b => { b with val := ⟨0, Nat.zero_lt_succ 0⟩ }

instance (priority := 100) instBoxNonempty (n : ℕ) : Nonempty (Box n) :=
  ⟨{ val := ⟨0, Nat.zero_lt_succ n⟩ } |> fun b => { b with val := ⟨0, Nat.zero_lt_succ 0⟩ }⟩

theorem box_val_zero (b : Box 0) : b.val = ⟨0, Nat.zero_lt_succ 0⟩ := by
  rcases b with ⟨⟨v, hv⟩⟩; simp only [Nat.lt_one_iff] at hv; subst hv; rfl

example (b : Box 0) : b.val = ⟨0, Nat.zero_lt_succ 0⟩ := by
  rcases b with ⟨⟨v, hv⟩⟩; simp only [Nat.lt_one_iff] at hv; subst hv; rfl

end Fixture
