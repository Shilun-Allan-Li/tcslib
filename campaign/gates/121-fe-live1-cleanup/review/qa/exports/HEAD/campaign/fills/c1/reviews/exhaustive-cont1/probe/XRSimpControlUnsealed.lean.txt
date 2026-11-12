import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam

namespace Turing
/-- Seal control 6 (simp): closes only by simp unfolding `Turing.Cfg.init`. -/
example {k : ℕ} {x : List Bool} (q : Bool) : (Cfg.init (k := k) q x).output = [] := by simp

/-- Seal control 7 (simp): closes only by simp unfolding `Turing.Action.apply`. -/
example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :
    (a.apply c).state = a.state := by simp
end Turing
