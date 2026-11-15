import TCSlib.Complexity.ClassP.DTIME

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DerandEvidence

-- This positive interface use must remain available when the definition is sealed.
example {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ Complexity.DTIME T ↔
      ∃ (c : ℕ) (M : Turing.FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Complexity.mem_DTIME_iff

-- The deliberate hidden-definition read must fail exactly once when sealed.
example {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ Complexity.DTIME T ↔
      ∃ (c : ℕ) (M : Turing.FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl

end DerandEvidence
