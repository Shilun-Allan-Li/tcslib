import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam
set_option maxHeartbeats 0

namespace Turing
/-- Seal control 1: closes only by unfolding `Turing.MultiTapeTM.runFrom`. -/
example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :
    tm.runFrom c 0 = c := rfl

/-- Seal control 2: closes only by unfolding `Turing.FinTM.bufferTape`. -/
example : FinTM.bufferTape [true] 0 = some true := by rfl

/-- Seal control 3: closes only by unfolding `Turing.NDTM.runWith`. -/
example {k : ℕ} {S : Type} {x : List Bool} (N : NDTM k Bool S) (c : Cfg k Bool S x) :
    N.runWith [] c = c := rfl
end Turing
