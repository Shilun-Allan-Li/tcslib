import Lean
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
