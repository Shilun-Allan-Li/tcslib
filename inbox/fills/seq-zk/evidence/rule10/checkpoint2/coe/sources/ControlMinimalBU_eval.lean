import Lean
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl

theorem positive (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := Complexity.PolyExpr.eval_const 2 n

end HashSignSensitivity

