import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 400000
set_option autoImplicit false

/-! Controls for the seal of the efficiency fill: six readings of definitions through their
bodies. In `SealControlsSealed` (every foreign definition of the scan sealed) each must FAIL;
in `SealControlsUnsealed` each must PASS. -/

namespace TCSlib.Cryptography.Games.SealCtl

open Complexity Turing

attribute [local irreducible] _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyTimeComputable _root_.Complexity.StateLoop.orbit _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.encodeHist _root_.Turing.pairDecode _root_.Turing.pairEncode

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
