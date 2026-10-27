import sys
src, dst = sys.argv[1], sys.argv[2]
t = open(src, encoding="utf-8").read()
standin = '''/-! ### Stand-in for A1's reading (proved before the seal; published by #164) -/

theorem qy_timeConstructible_iff (T : ℕ → ℕ) :
    Complexity.TimeConstructible T ↔
      (∀ n, n ≤ T n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
        M.ComputesInTime x (T x.length).bits (c * (T x.length + 1)) :=
  Iff.rfl

'''
assert t.count(standin) == 1, "stand-in block not found exactly once"
t = t.replace(standin, "")
old = "(qy_timeConstructible_iff f).mp hf"
assert t.count(old) == 1
t = t.replace(old, "(Complexity.timeConstructible_iff f).mp hf")
oldc = '''At the drafting base A1's `Complexity.timeConstructible_iff` is not yet published, so it has a
local stand-in proved by `Iff.rfl` before the seal; at issue (after #164) the probe cites it.'''
assert t.count(oldc) == 1
t = t.replace(oldc, "Review re-run at the tip: A1's `Complexity.timeConstructible_iff` is cited; the stand-in is removed.")
assert "qy_timeConstructible_iff" not in t
open(dst, "w", encoding="utf-8").write(t)
print("ok")
