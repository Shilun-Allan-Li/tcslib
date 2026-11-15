import Lean
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := rfl

theorem positive (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := Complexity.NUPPT.inArg_eq z

end HashSignSensitivity

