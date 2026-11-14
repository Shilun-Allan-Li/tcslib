import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
import Mathlib.Data.List.OfFn

set_option maxHeartbeats 0
example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
