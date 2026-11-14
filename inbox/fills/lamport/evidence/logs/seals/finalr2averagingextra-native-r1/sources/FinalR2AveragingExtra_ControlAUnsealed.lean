import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
example (x : ℝ) : TCSlib.Cryptography.Games.ProbComp.expect (.pure x) (fun y => y) = x := by
  rfl
