import Lean
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
