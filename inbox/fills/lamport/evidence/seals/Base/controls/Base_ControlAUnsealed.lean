import Lean
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
