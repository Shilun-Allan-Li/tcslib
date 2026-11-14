import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
