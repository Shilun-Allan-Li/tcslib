import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 400000
set_option autoImplicit false

/-! Controls for the seal of the efficiency fill: six readings of definitions through their
bodies. In `SealControlsSealed` (every foreign definition of the scan sealed) each must FAIL;
in `SealControlsUnsealed` each must PASS. -/

namespace TCSlib.Cryptography.Games.SealCtl

open Complexity Turing

/-- C1: the pairing `Turing.pairEncode` read through its body. -/
example (a b : List Bool) : Turing.pairEncode a b = (a.flatMap fun x => [x, x]) ++ [false, true] ++ b :=
  rfl

/-- C2: the log encoding `MachineCodec.encodeLog` of the empty log read through its body. -/
example (d : Fin 2 → ℕ) : (bitCodec d d 3).encodeLog [] = [] := rfl

/-- C3: the helper `EffFill.fixLen` read through its body. -/
example (w : List Bool) : EffFill.fixLen 2 w = if w.length = 2 then w else [false, false] := rfl

/-- C4: `PolyExpr.eval` of a constant read through its body. -/
example (n : ℕ) : PolyExpr.eval (.const 3) n = 3 := rfl

/-- C5: `buildComp` at budget `0` on a return read through its body. -/
example (a : Bool) : buildComp (spec := bitSpec (fun _ : Fin 1 => 0) (fun _ => 0))
    (fun _ => Move.ret a) false 0 [] = .pure a := rfl

/-- C6: the activation loop `EffFill.actLoop` read through its body. -/
example (s a : List Bool → List Bool) (R B : PolyExpr) :
    EffFill.actLoop s a R B = GGMRed.stateLoopFun s (EffFill.actStep a) (EffFill.actAcc a)
      (EffFill.actStep a) R B := rfl

end TCSlib.Cryptography.Games.SealCtl
