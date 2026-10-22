import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam
set_option maxHeartbeats 0

namespace Turing
/-- Seal control 4 (end of the section): closes only by unfolding `Turing.MultiTapeTM.runFrom`. -/
example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :
    tm.runFrom c 0 = c := by rfl

/-- Seal control 5 (end of the section): closes only by unfolding `Turing.Cfg.mapState`. -/
example {k : ℕ} {S S' : Type} {x : List Bool} (c : Cfg k Bool S x) (f : S → S') :
    (c.mapState f).output = c.output := rfl
end Turing
