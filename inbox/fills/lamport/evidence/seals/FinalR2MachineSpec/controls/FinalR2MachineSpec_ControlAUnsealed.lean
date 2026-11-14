import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
