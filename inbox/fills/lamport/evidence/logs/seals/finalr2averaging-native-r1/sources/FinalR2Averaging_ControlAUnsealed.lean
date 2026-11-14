import Lean
import TCSlib.Cryptography.Games.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
example (x : ℝ) : TCSlib.Cryptography.Games.ProbComp.expect (.pure x) (fun y => y) = x := by
  rfl
