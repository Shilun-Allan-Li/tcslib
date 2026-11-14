import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
