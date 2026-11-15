"""Apply only the two pre-approved DTIME readers; no existing bytes are changed."""
from pathlib import Path

path = Path('TCSlib/Complexity/ClassP/DTIME.lean')
src = path.read_text()
reader = '''/-- The decision contract `M.DecidesInTime L T` holds exactly when every input `x`
is computed with output `[indicator L x]` within `T |x|` steps:
`M.DecidesInTime L T ↔ ∀ x, M.ComputesInTime x [indicator L x] (T |x|)`.
[AB09, §1.6, Definition 1.3] -/
theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    M.DecidesInTime L T ↔
      ∀ x : List Bool,
        M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length) :=
  Iff.rfl

'''
src = src.replace('end Turing.FinTM', reader + 'end Turing.FinTM', 1)
reader = '''/-- Membership `L ∈ DTIME T` is exactly a constant `c` and a finite machine `M`
deciding `L` within `n ↦ c * T n`:
`L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L (fun n => c * T n)`.
[AB09, Definition 1.12] -/
theorem mem_DTIME_iff {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl

'''
src = src.replace('/-- `DTIME` is monotone in the time bound.',
                  reader + '/-- `DTIME` is monotone in the time bound.', 1)
path.write_text(src)
