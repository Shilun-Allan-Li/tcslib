import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
