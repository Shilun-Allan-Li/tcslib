/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The replay machine of an interactive handler (efficiency fill, T2)

The raw function behind `Games.exists_interactiveHandlerMachine` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T2"), over the raw ingredients of an
interactive handler. Its functional equation is in
`TCSlib.Cryptography.Games.Efficiency.InteractiveSpec`.

The machine is an oracle machine against the outer oracles. On the raw layout
`X = ⟨⟨⟨1^n, ⟨⟨z, O⟩, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩`, where `O` is its own encoded outer log, it replays the
whole reduction in an activation loop (`EffFill.actLoop`), one activation per round, on the state
`⟨ph, ⟨L, ⟨s, ⟨1^b, ⟨cur, ⟨L', ⟨1^c, O'⟩⟩⟩⟩⟩⟩⟩` (`iSt`):
- the phase `ph`: `[]` the adversary, `[true]` a call of the handler, `[false]` the finalization;
- the adversary's encoded log `L`, the handler's state `s` and the adversary's remaining budget `b`;
- in a call, the pending inner query `cur = ⟨1^i, x⟩`; in the finalization, the adversary's output
  `cur = a`;
- the outer log `L'` of the current call or finalization, and its remaining budget `c`;
- the part `O'` of `O` not yet replayed.

A round of the adversary runs `A` and opens a call (a query within budget) or the finalization (an
output, or a query at budget `0` with the all-`false` output). A round of a call runs `run` on
`⟨ctx, ⟨s, ⟨cur, L'⟩⟩⟩`: its answer `⟨y, s'⟩` (or the joint default at budget `0`) appends the
entry to `L` and returns to the adversary; an outer query is answered by the next entry of `O'`,
or, if `O'` is exhausted, **is the machine's next move**. The finalization runs `finRun` the same
way and stops with its output.

## Main definitions

* `EffFill.iSt`: the state word; `EffFill.iAct`, `EffFill.iStart`, `EffFill.iRaw`: the round, the
  initial state and the raw function; `EffFill.iRounds`, `EffFill.iBound`: the bounds.

## Main results

* `EffFill.iRaw_poly`: the raw function is polynomial-time.
* `EffFill.iAct_adv_ret`, …, `EffFill.iAct_fin_ask`: the round on each kind of state.
* `EffFill.length_iSt_le`: the state bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations; for example the reductions of the
  proofs of Theorems 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! Seal of the efficiency fill (s2b-efficiency): a verbatim copy of `TCSlib/Cryptography/Games/Efficiency/Interactive.lean` with every foreign
non-reducible TCSlib definition its declarations use made irreducible (scan: `SealScan.lean`). -/
attribute [local irreducible] _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.output _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.Turing.pairEncode


variable {k k' : ℕ}

/-! ### The state word -/

/-- The state word `⟨ph, ⟨L, ⟨s, ⟨bA, ⟨cur, ⟨L', ⟨c, O'⟩⟩⟩⟩⟩⟩⟩` of the replay machine. -/
def iSt (ph L s bA cur L' c O' : List Bool) : List Bool :=
  pairEncode ph (pairEncode L (pairEncode s (pairEncode bA (pairEncode cur
    (pairEncode L' (pairEncode c O'))))))

/-- The defining equation of `iSt`. -/
theorem iSt_eq (ph L s bA cur L' c O' : List Bool) :
    iSt ph L s bA cur L' c O' = pairEncode ph (pairEncode L (pairEncode s (pairEncode bA
      (pairEncode cur (pairEncode L' (pairEncode c O')))))) :=
  rfl

/-- The phase of a state word. -/
def gPh (S : List Bool) : List Bool := pairFstD S
/-- The adversary's log of a state word. -/
def gLin (S : List Bool) : List Bool := pairFstD (pairSndD S)
/-- The handler's state of a state word. -/
def gS (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD S))
/-- The adversary's remaining budget of a state word. -/
def gB (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD S)))
/-- The pending query or output of a state word. -/
def gCur (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (pairSndD S))))
/-- The outer log of the current call or finalization. -/
def gLc (S : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD S)))))
/-- The remaining budget of the current call or finalization. -/
def gC (S : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD S))))))
/-- The part of the outer log not yet replayed. -/
def gO (S : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD S))))))

section Read

variable (ph L s bA cur L' c O' : List Bool)

/-- `gPh (iSt ph …) = ph`. -/
theorem gPh_iSt : gPh (iSt ph L s bA cur L' c O') = ph := by
  simp only [gPh, iSt_eq, pairFstD_pairEncode]
/-- `gLin (iSt ph L …) = L`. -/
theorem gLin_iSt : gLin (iSt ph L s bA cur L' c O') = L := by
  simp only [gLin, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gS (iSt ph L s …) = s`. -/
theorem gS_iSt : gS (iSt ph L s bA cur L' c O') = s := by
  simp only [gS, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gB (iSt … bA …) = bA`. -/
theorem gB_iSt : gB (iSt ph L s bA cur L' c O') = bA := by
  simp only [gB, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gCur (iSt … cur …) = cur`. -/
theorem gCur_iSt : gCur (iSt ph L s bA cur L' c O') = cur := by
  simp only [gCur, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gLc (iSt … L' …) = L'`. -/
theorem gLc_iSt : gLc (iSt ph L s bA cur L' c O') = L' := by
  simp only [gLc, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gC (iSt … c O') = c`. -/
theorem gC_iSt : gC (iSt ph L s bA cur L' c O') = c := by
  simp only [gC, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gO (iSt … O') = O'`. -/
theorem gO_iSt : gO (iSt ph L s bA cur L' c O') = O' := by
  simp only [gO, iSt_eq, pairSndD_pairEncode]

end Read

/-- The context `⟨1^n, ⟨z, ω⟩⟩` read off the raw layout `⟨⟨⟨1^n, ⟨⟨z, O⟩, ω⟩⟩, α⟩, r⟩`. -/
def iCtx (X : List Bool) : List Bool :=
  pairEncode (NUPPT.inParam X)
    (pairEncode (pairFstD (pairFstD (NUPPT.inArg X))) (pairSndD (NUPPT.inArg X)))

/-- The defining equation of `iCtx`. -/
theorem iCtx_eq (X : List Bool) : iCtx X = pairEncode (NUPPT.inParam X)
    (pairEncode (pairFstD (pairFstD (NUPPT.inArg X))) (pairSndD (NUPPT.inArg X))) :=
  rfl

/-- The machine's own outer log `O`, read off the raw layout. -/
def iOuter (X : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg X))

/-- `iOuter X = snd (fst (inArg X))`. -/
theorem iOuter_eq (X : List Bool) : iOuter X = pairSndD (pairFstD (NUPPT.inArg X)) := rfl

/-! ### The rounds -/

section Raw

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' : Fin k' → PolyExpr)
  (stateLen perCall outLen finCall : PolyExpr) (run advIn finRun : List Bool → List Bool)

/-- The adversary's canonical move word in a round of the adversary phase. -/
def iAdvMove (w : List Bool) : List Bool :=
  canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
      (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
        (pairEncode (advIn (iCtx (pairFstD w))) (gLin (pairSndD w)))
        (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w))))))

/-- The defining equation of `iAdvMove`. -/
theorem iAdvMove_eq (w : List Bool) :
    iAdvMove A dα din advIn w =
      canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
          (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
            (pairEncode (advIn (iCtx (pairFstD w))) (gLin (pairSndD w)))
            (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w)))))) :=
  rfl

/-- **A round of the adversary:** an output `a` opens the finalization with `cur = a`; a query at
budget `0` opens it with `0^{dα(n)}`; a query within budget opens a call with `cur = ⟨1^i, x⟩`. -/
def iAdvAct (w : List Bool) : List Bool :=
  if pairFstD (iAdvMove A dα din advIn w) = [true] then
    pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
      (pairSndD (iAdvMove A dα din advIn w)) []
      (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true) (gO (pairSndD w)))
  else if gB (pairSndD w) = [] then
    pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
      (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false) []
      (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true) (gO (pairSndD w)))
  else
    pairEncode [false] (iSt [true] (gLin (pairSndD w)) (gS (pairSndD w)) ((gB (pairSndD w)).drop 1)
      (pairSndD (iAdvMove A dα din advIn w)) []
      (List.replicate (perCall.eval (NUPPT.inParam (pairFstD w)).length) true) (gO (pairSndD w)))

/-- The defining equation of `iAdvAct`. -/
theorem iAdvAct_eq (w : List Bool) :
    iAdvAct A dα din perCall finCall advIn w =
      if pairFstD (iAdvMove A dα din advIn w) = [true] then
        pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
          (pairSndD (iAdvMove A dα din advIn w)) []
          (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true)
          (gO (pairSndD w)))
      else if gB (pairSndD w) = [] then
        pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
          (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false) []
          (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true)
          (gO (pairSndD w)))
      else
        pairEncode [false] (iSt [true] (gLin (pairSndD w)) (gS (pairSndD w))
          ((gB (pairSndD w)).drop 1) (pairSndD (iAdvMove A dα din advIn w)) []
          (List.replicate (perCall.eval (NUPPT.inParam (pairFstD w)).length) true)
          (gO (pairSndD w))) :=
  rfl

/-- The length `dout i (n)` of the answer to the pending query `cur = ⟨1^i, x⟩`. -/
def iAnsLen (w : List Bool) : ℕ :=
  selLen dout (NUPPT.inParam (pairFstD w)).length (pairFstD (gCur (pairSndD w))).length

/-- `iAnsLen w = selLen dout n |fst cur|`. -/
theorem iAnsLen_eq (w : List Bool) : iAnsLen dout w =
    selLen dout (NUPPT.inParam (pairFstD w)).length (pairFstD (gCur (pairSndD w))).length :=
  rfl

/-- The handler's canonical move word in a round of a call (result length `dout i + stateLen`). -/
def iCallMove (w : List Bool) : List Bool :=
  canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length)
      true)
      (run (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
        (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w))))))))

/-- The defining equation of `iCallMove`. -/
theorem iCallMove_eq (w : List Bool) :
    iCallMove dout din' stateLen run w =
      canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (iAnsLen dout w +
            stateLen.eval (NUPPT.inParam (pairFstD w)).length) true)
          (run (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
            (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w)))))))) :=
  rfl

/-- The end of a call with result `W = y ‖ s'`: the entry `⟨1^i, ⟨x, y⟩⟩` is appended to the
adversary's log, the state becomes `s'`, and the phase returns to the adversary. -/
def iCallEnd (w W : List Bool) : List Bool :=
  iSt [] (gLin (pairSndD w) ++ pairEncode (pairEncode (pairFstD (gCur (pairSndD w)))
      (pairEncode (pairSndD (gCur (pairSndD w))) (W.take (iAnsLen dout w)))) [])
    (W.drop (iAnsLen dout w)) (gB (pairSndD w)) [] [] [] (gO (pairSndD w))

/-- The defining equation of `iCallEnd`. -/
theorem iCallEnd_eq (w W : List Bool) :
    iCallEnd dout w W =
      iSt [] (gLin (pairSndD w) ++ pairEncode (pairEncode (pairFstD (gCur (pairSndD w)))
          (pairEncode (pairSndD (gCur (pairSndD w))) (W.take (iAnsLen dout w)))) [])
        (W.drop (iAnsLen dout w)) (gB (pairSndD w)) [] [] [] (gO (pairSndD w)) :=
  rfl

/-- An outer query answered from the replayed log: the next entry of `O'` is appended to the
current outer log, its budget decreases, and the phase `ph` continues. -/
def iAsk (ph w : List Bool) : List Bool :=
  iSt ph (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w)) (gCur (pairSndD w))
    (gLc (pairSndD w) ++ pairEncode (pairFstD (gO (pairSndD w))) []) ((gC (pairSndD w)).drop 1)
    (pairSndD (gO (pairSndD w)))

/-- The defining equation of `iAsk`. -/
theorem iAsk_eq (ph w : List Bool) :
    iAsk ph w = iSt ph (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w)) (gCur (pairSndD w))
      (gLc (pairSndD w) ++ pairEncode (pairFstD (gO (pairSndD w))) []) ((gC (pairSndD w)).drop 1)
      (pairSndD (gO (pairSndD w))) :=
  rfl

/-- **A round of a call:** an answer ends the call; a query at budget `0` ends it with the joint
all-`false` default; a query within budget is answered from the replayed log or, when that is
exhausted, is the machine's move. -/
def iCallAct (w : List Bool) : List Bool :=
  if pairFstD (iCallMove dout din' stateLen run w) = [true] then
    pairEncode [false] (iCallEnd dout w (pairSndD (iCallMove dout din' stateLen run w)))
  else if gC (pairSndD w) = [] then
    pairEncode [false] (iCallEnd dout w (List.replicate
      (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length) false))
  else if gO (pairSndD w) = [] then pairEncode [true] (iCallMove dout din' stateLen run w)
  else pairEncode [false] (iAsk [true] w)

/-- The defining equation of `iCallAct`. -/
theorem iCallAct_eq (w : List Bool) :
    iCallAct dout din' stateLen run w =
      if pairFstD (iCallMove dout din' stateLen run w) = [true] then
        pairEncode [false] (iCallEnd dout w (pairSndD (iCallMove dout din' stateLen run w)))
      else if gC (pairSndD w) = [] then
        pairEncode [false] (iCallEnd dout w (List.replicate
          (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length) false))
      else if gO (pairSndD w) = [] then pairEncode [true] (iCallMove dout din' stateLen run w)
      else pairEncode [false] (iAsk [true] w) :=
  rfl

/-- The finalization's canonical move word in a round of the finalization. -/
def iFinMove (w : List Bool) : List Bool :=
  canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) true)
      (finRun (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
        (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w))))))))

/-- The defining equation of `iFinMove`. -/
theorem iFinMove_eq (w : List Bool) :
    iFinMove din' outLen finRun w =
      canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) true)
          (finRun (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
            (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w)))))))) :=
  rfl

/-- **A round of the finalization:** an output stops with its word; a query at budget `0` stops
with `⟨[true], 0^{outLen(n)}⟩`; a query within budget is answered from the replayed log or, when
that is exhausted, is the machine's move. -/
def iFinAct (w : List Bool) : List Bool :=
  if pairFstD (iFinMove din' outLen finRun w) = [true] then
    pairEncode [true] (iFinMove din' outLen finRun w)
  else if gC (pairSndD w) = [] then
    pairEncode [true] (pairEncode [true]
      (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) false))
  else if gO (pairSndD w) = [] then pairEncode [true] (iFinMove din' outLen finRun w)
  else pairEncode [false] (iAsk [false] w)

/-- The defining equation of `iFinAct`. -/
theorem iFinAct_eq (w : List Bool) :
    iFinAct din' outLen finRun w =
      if pairFstD (iFinMove din' outLen finRun w) = [true] then
        pairEncode [true] (iFinMove din' outLen finRun w)
      else if gC (pairSndD w) = [] then
        pairEncode [true] (pairEncode [true]
          (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) false))
      else if gO (pairSndD w) = [] then pairEncode [true] (iFinMove din' outLen finRun w)
      else pairEncode [false] (iAsk [false] w) :=
  rfl

/-- **One round of the replay machine**, by phase. -/
def iAct (w : List Bool) : List Bool :=
  if gPh (pairSndD w) = [] then iAdvAct A dα din perCall finCall advIn w
  else if gPh (pairSndD w) = [true] then iCallAct dout din' stateLen run w
  else iFinAct din' outLen finRun w

/-- The defining equation of `iAct`. -/
theorem iAct_eq (w : List Bool) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun w =
      if gPh (pairSndD w) = [] then iAdvAct A dα din perCall finCall advIn w
      else if gPh (pairSndD w) = [true] then iCallAct dout din' stateLen run w
      else iFinAct din' outLen finRun w :=
  rfl

/-- The initial state: the adversary's phase, empty log, the initial state `s₀` read off the
advice, the budget `1^{q(n)}`, and the whole outer log `O` still to replay. -/
def iStart (X : List Bool) : List Bool :=
  iSt [] [] (pairSndD (NUPPT.inAdvice X)) (List.replicate (q.eval (NUPPT.inParam X).length) true)
    [] [] [] (iOuter X)

/-- The defining equation of `iStart`. -/
theorem iStart_eq (X : List Bool) :
    iStart q X = iSt [] [] (pairSndD (NUPPT.inAdvice X))
      (List.replicate (q.eval (NUPPT.inParam X).length) true) [] [] [] (iOuter X) :=
  rfl

/-- The round bound `2 + finCall + q (perCall + 2)`: at most `q + 1` rounds of the adversary,
`perCall + 1` rounds per call and `finCall + 1` rounds of the finalization. -/
def iRounds : PolyExpr := .add (.add (.const 2) finCall) (.mul q (.add perCall (.const 2)))

/-- The defining equation of `iRounds`. -/
theorem iRounds_eq : iRounds q perCall finCall =
    .add (.add (.const 2) finCall) (.mul q (.add perCall (.const 2))) :=
  rfl

/-- The bound on the pending query or output: `2k + 2 + 2 Σ din + dα`. -/
def iCurBound : PolyExpr := .add (.const (2 * k + 2)) (.add (.mul (.const 2) (sumPoly din)) dα)

/-- The defining equation of `iCurBound`. -/
theorem iCurBound_eq : iCurBound dα din =
    .add (.const (2 * k + 2)) (.add (.mul (.const 2) (sumPoly din)) dα) :=
  rfl

/-- The fixed-length part of the state bound:
`16 + 2 (q E + stateLen + q + cur + (perCall + finCall)(E' + 1))`, with the entry bounds `E`, `E'`
of the inner and outer logs and the bound `cur` on the pending query or output. -/
def iFixBound (dout' : Fin k' → PolyExpr) : PolyExpr :=
  .add (.const 16) (.mul (.const 2) (.add (.mul q (entryPoly din dout)) (.add stateLen (.add q
    (.add (iCurBound dα din) (.mul (.add perCall finCall) (.add (entryPoly din' dout') (.const
        1))))))))

/-- The defining equation of `iFixBound`. -/
theorem iFixBound_eq (dout' : Fin k' → PolyExpr) :
    iFixBound q dα din dout din' stateLen perCall finCall dout' =
      .add (.const 16) (.mul (.const 2) (.add (.mul q (entryPoly din dout)) (.add stateLen (.add q
        (.add (iCurBound dα din)
          (.mul (.add perCall finCall) (.add (entryPoly din' dout') (.const 1)))))))) :=
  rfl

/-- The state bound: the fixed-length part plus `|X|` for the part of the outer log not yet
replayed. -/
def iBound (dout' : Fin k' → PolyExpr) : PolyExpr :=
  .add (iFixBound q dα din dout din' stateLen perCall finCall dout') .var

/-- `iBound = iFixBound + var`. -/
theorem iBound_eq (dout' : Fin k' → PolyExpr) :
    iBound q dα din dout din' stateLen perCall finCall dout' =
      .add (iFixBound q dα din dout din' stateLen perCall finCall dout') .var :=
  rfl

/-- **The raw function of the replay machine:** the activation loop of `iAct` from `iStart`. -/
def iRaw (dout' : Fin k' → PolyExpr) : List Bool → List Bool :=
  actLoop (iStart q) (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
    (iRounds q perCall finCall) (iBound q dα din dout din' stateLen perCall finCall dout')

/-- `iRaw = actLoop iStart iAct iRounds iBound`. -/
theorem iRaw_eq (dout' : Fin k' → PolyExpr) :
    iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun dout' =
      actLoop (iStart q) (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
        (iRounds q perCall finCall) (iBound q dα din dout din' stateLen perCall finCall dout') :=
  rfl

/-! ### Polynomial time -/

variable {run advIn finRun}

/-- The state word of polynomial-time components is polynomial-time. -/
theorem iSt_poly {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) (h₄ : PolyTimeComputable f₄)
    (h₅ : PolyTimeComputable f₅) (h₆ : PolyTimeComputable f₆) (h₇ : PolyTimeComputable f₇)
    (h₈ : PolyTimeComputable f₈) :
    PolyTimeComputable fun w => iSt (f₁ w) (f₂ w) (f₃ w) (f₄ w) (f₅ w) (f₆ w) (f₇ w) (f₈ w) :=
  (h₁.pairEncode (h₂.pairEncode (h₃.pairEncode (h₄.pairEncode (h₅.pairEncode
    (h₆.pairEncode (h₇.pairEncode h₈))))))).congr fun _ => (iSt_eq _ _ _ _ _ _ _ _).symm

/-- The components of the state word of `w = ⟨X, S⟩` are polynomial-time in `w`. -/
theorem gS_comps_poly :
    PolyTimeComputable (fun w => gPh (pairSndD w)) ∧ PolyTimeComputable (fun w => gLin (pairSndD w))
        ∧
    PolyTimeComputable (fun w => gS (pairSndD w)) ∧ PolyTimeComputable (fun w => gB (pairSndD w)) ∧
    PolyTimeComputable (fun w => gCur (pairSndD w)) ∧ PolyTimeComputable (fun w => gLc (pairSndD w))
        ∧
    PolyTimeComputable (fun w => gC (pairSndD w)) ∧ PolyTimeComputable (fun w => gO (pairSndD w)) :=
        by
  have f := polyTimeComputable_pairFstD
  have g := polyTimeComputable_pairSndD
  refine ⟨f.comp' g, f.comp' (g.comp' g), f.comp' (g.comp' (g.comp' g)),
    f.comp' (g.comp' (g.comp' (g.comp' g))), f.comp' (g.comp' (g.comp' (g.comp' (g.comp' g)))),
    f.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' g))))),
    f.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' g)))))),
    g.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' g))))))⟩

/-- The context is polynomial-time. -/
theorem iCtx_poly : PolyTimeComputable iCtx :=
  NUPPT.polyTimeComputable_inParam.pairEncode
    ((polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp'
      NUPPT.polyTimeComputable_inArg)).pairEncode
      (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg))

/-- The adversary's move word is polynomial-time. -/
theorem iAdvMove_poly (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (iAdvMove A dα din advIn) := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hout := A.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    ((hadvIn.comp' (iCtx_poly.comp' hX)).pairEncode gS_comps_poly.2.1)
    (polyTimeComputable_pairFstD.comp' (NUPPT.polyTimeComputable_inAdvice.comp' hX))
    (NUPPT.polyTimeComputable_inCoins.comp' hX))
  exact (canonFun_poly din).comp' (hu.pairEncode ((StateLoop.unaryPoly_comp dα hu).pairEncode hout))

/-- A round of the adversary is polynomial-time. -/
theorem iAdvAct_poly (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (iAdvAct A dα din perCall finCall advIn) := by
  obtain ⟨-, hL, hs, hb, -, -, -, hO⟩ := gS_comps_poly
  have hu := NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD
  have hm := iAdvMove_poly A dα din hadvIn
  have hfin := StateLoop.unaryPoly_comp finCall hu
  have hz : PolyTimeComputable fun w =>
      List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false :=
    (zeros_poly (StateLoop.unaryPoly_comp dα hu)).congr fun w => by rw [List.length_replicate]
  have h := polyTimeComputable_ite (eq_poly (polyTimeComputable_pairFstD.comp' hm)
      (polyTimeComputable_const [true]))
    ((polyTimeComputable_const [false]).pairEncode (iSt_poly (polyTimeComputable_const [false]) hL
        hs
      hb (polyTimeComputable_pairSndD.comp' hm) (polyTimeComputable_const []) hfin hO))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' hb)
      ((polyTimeComputable_const [false]).pairEncode (iSt_poly (polyTimeComputable_const [false])
        hL hs hb hz (polyTimeComputable_const []) hfin hO))
      ((polyTimeComputable_const [false]).pairEncode (iSt_poly (polyTimeComputable_const [true])
        hL hs (polyTimeComputable_tail.comp' hb) (polyTimeComputable_pairSndD.comp' hm)
        (polyTimeComputable_const []) (StateLoop.unaryPoly_comp perCall hu) hO)))
  refine h.congr fun w => ?_
  rw [iAdvAct_eq]
  simp only [decide_eq_true_eq]

/-- The answer length `dout i (n)`, in unary, is polynomial-time. -/
theorem iAnsLen_poly : PolyTimeComputable fun w => List.replicate (iAnsLen dout w) true :=
  ((selLen_poly dout).comp' ((NUPPT.polyTimeComputable_inParam.comp'
      polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_pairFstD.comp' gS_comps_poly.2.2.2.2.1))).congr fun w => by
    rw [iAnsLen_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The result length `dout i (n) + stateLen(n)`, in unary, is polynomial-time. -/
theorem iResLen_poly : PolyTimeComputable fun w => List.replicate
    (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length) true :=
  ((iAnsLen_poly dout).append (StateLoop.unaryPoly_comp stateLen
    (NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD))).congr fun w => by
    rw [List.replicate_add]

/-- The handler's input `⟨ctx, ⟨s, ⟨cur, L'⟩⟩⟩` is polynomial-time. -/
theorem iHInput_poly : PolyTimeComputable fun w => pairEncode (iCtx (pairFstD w))
    (pairEncode (gS (pairSndD w)) (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w)))) :=
  (iCtx_poly.comp' polyTimeComputable_pairFstD).pairEncode (gS_comps_poly.2.2.1.pairEncode
    (gS_comps_poly.2.2.2.2.1.pairEncode gS_comps_poly.2.2.2.2.2.1))

/-- The handler's move word in a call is polynomial-time. -/
theorem iCallMove_poly (hrun : PolyTimeComputable run) :
    PolyTimeComputable (iCallMove dout din' stateLen run) :=
  (canonFun_poly din').comp' ((NUPPT.polyTimeComputable_inParam.comp'
    polyTimeComputable_pairFstD).pairEncode ((iResLen_poly dout stateLen).pairEncode
      (hrun.comp' iHInput_poly)))

/-- The end of a call with a polynomial-time result is polynomial-time. -/
theorem iCallEnd_poly {W : List Bool → List Bool} (hW : PolyTimeComputable W) :
    PolyTimeComputable fun w => iCallEnd dout w (W w) := by
  obtain ⟨-, hL, -, hb, hcur, -, -, hO⟩ := gS_comps_poly
  have hdl := iAnsLen_poly dout
  have h := iSt_poly (polyTimeComputable_const []) (hL.append
      (((polyTimeComputable_pairFstD.comp' hcur).pairEncode
        ((polyTimeComputable_pairSndD.comp' hcur).pairEncode (takeLen_poly hdl hW))).pairEncode
        (polyTimeComputable_const [])))
    (dropLen_poly hdl hW) hb (polyTimeComputable_const []) (polyTimeComputable_const [])
    (polyTimeComputable_const []) hO
  refine h.congr fun w => ?_
  rw [iCallEnd_eq, List.length_replicate]

/-- Answering an outer query from the replayed log is polynomial-time. -/
theorem iAsk_poly (ph : List Bool) : PolyTimeComputable (iAsk ph) := by
  obtain ⟨-, hL, hs, hb, hcur, hLc, hc, hO⟩ := gS_comps_poly
  exact (iSt_poly (polyTimeComputable_const ph) hL hs hb hcur
    (hLc.append ((polyTimeComputable_pairFstD.comp' hO).pairEncode (polyTimeComputable_const [])))
    (polyTimeComputable_tail.comp' hc) (polyTimeComputable_pairSndD.comp' hO)).congr fun w =>
    (iAsk_eq ph w).symm

/-- A round of a call is polynomial-time. -/
theorem iCallAct_poly (hrun : PolyTimeComputable run) :
    PolyTimeComputable (iCallAct dout din' stateLen run) := by
  have hm := iCallMove_poly dout din' stateLen hrun
  have h := polyTimeComputable_ite (eq_poly (polyTimeComputable_pairFstD.comp' hm)
      (polyTimeComputable_const [true]))
    ((polyTimeComputable_const [false]).pairEncode
      (iCallEnd_poly dout (polyTimeComputable_pairSndD.comp' hm)))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.1)
      ((polyTimeComputable_const [false]).pairEncode
        (iCallEnd_poly dout ((zeros_poly (iResLen_poly dout stateLen)).congr fun w => by
          rw [List.length_replicate])))
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.2)
        ((polyTimeComputable_const [true]).pairEncode hm)
        ((polyTimeComputable_const [false]).pairEncode (iAsk_poly [true]))))
  refine h.congr fun w => ?_
  rw [iCallAct_eq]
  simp only [decide_eq_true_eq]

/-- The finalization's move word is polynomial-time. -/
theorem iFinMove_poly (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iFinMove din' outLen finRun) :=
  (canonFun_poly din').comp' ((NUPPT.polyTimeComputable_inParam.comp'
    polyTimeComputable_pairFstD).pairEncode ((StateLoop.unaryPoly_comp outLen
      (NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD)).pairEncode
      (hfinRun.comp' iHInput_poly)))

/-- A round of the finalization is polynomial-time. -/
theorem iFinAct_poly (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iFinAct din' outLen finRun) := by
  have hm := iFinMove_poly din' outLen hfinRun
  have hu := NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD
  have hz : PolyTimeComputable fun w =>
      List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) false :=
    (zeros_poly (StateLoop.unaryPoly_comp outLen hu)).congr fun w => by rw [List.length_replicate]
  have h := polyTimeComputable_ite (eq_poly (polyTimeComputable_pairFstD.comp' hm)
      (polyTimeComputable_const [true]))
    ((polyTimeComputable_const [true]).pairEncode hm)
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.1)
      ((polyTimeComputable_const [true]).pairEncode ((polyTimeComputable_const [true]).pairEncode
          hz))
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.2)
        ((polyTimeComputable_const [true]).pairEncode hm)
        ((polyTimeComputable_const [false]).pairEncode (iAsk_poly [false]))))
  refine h.congr fun w => ?_
  rw [iFinAct_eq]
  simp only [decide_eq_true_eq]

/-- **One round of the replay machine is polynomial-time.** -/
theorem iAct_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn)
    (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun) :=
        by
  have hph := gS_comps_poly.1
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hph)
    (iAdvAct_poly A dα din perCall finCall hadvIn)
    (polyTimeComputable_ite (eq_poly hph (polyTimeComputable_const [true]))
      (iCallAct_poly dout din' stateLen hrun) (iFinAct_poly din' outLen hfinRun))
  refine h.congr fun w => ?_
  rw [iAct_eq]
  simp only [decide_eq_true_eq]

/-- **The raw function of the replay machine is polynomial-time** (`actLoop_poly`). -/
theorem iRaw_poly (dout' : Fin k' → PolyExpr) (hrun : PolyTimeComputable run)
    (hadvIn : PolyTimeComputable advIn) (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun
      dout') := by
  have hstart : PolyTimeComputable (iStart q) :=
    (iSt_poly (polyTimeComputable_const []) (polyTimeComputable_const [])
      (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inAdvice)
      (StateLoop.unaryPoly_comp q NUPPT.polyTimeComputable_inParam) (polyTimeComputable_const [])
      (polyTimeComputable_const []) (polyTimeComputable_const [])
      (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp'
        NUPPT.polyTimeComputable_inArg))).congr fun X => (iStart_eq q X).symm
  exact actLoop_poly hstart (iAct_poly A dα din dout din' stateLen perCall outLen finCall hrun
    hadvIn hfinRun) _ _

end Raw

/-! ### The rounds on state words -/

section Rounds

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' : Fin k' → PolyExpr)
  (stateLen perCall outLen finCall : PolyExpr) (run advIn finRun : List Bool → List Bool)
  {X : List Bool} {n : ℕ}

/-- The adversary's move word on a state word: the canonical decoder of `A`'s output on
`⟨advIn ctx, L⟩` with the advice and coins of the layout. -/
theorem iAdvMove_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA cur L' c O' : List Bool) :
    iAdvMove A dα din advIn (pairEncode X (iSt ph L s bA cur L' c O')) =
      canonWord din n (dα.eval n) (A.output (NUPPT.layout (List.replicate n true)
        (pairEncode (advIn (iCtx X)) L) (pairFstD (NUPPT.inAdvice X)) (NUPPT.inCoins X))) := by
  rw [iAdvMove_eq, pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, hXu, List.length_replicate]
  exact canonFun_eq din n (dα.eval n) _

/-- **The adversary outputs:** the finalization opens with `cur = a` and budget `finCall(n)`. -/
theorem iAct_adv_ret (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA cur L' c O' a : List Bool}
    (hm : iAdvMove A dα din advIn (pairEncode X (iSt [] L s bA cur L' c O')) = pairEncode [true] a)
        :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [] L s bA cur L' c O')) =
      pairEncode [false] (iSt [false] L s bA a [] (List.replicate (finCall.eval n) true) O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_pos rfl, iAdvAct_eq, hm,
    if_pos (pairFstD_pairEncode _ _)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gO_iSt, hXu,
    List.length_replicate]

/-- **The adversary queries at budget `0`:** the finalization opens with `cur = 0^{dα(n)}`. -/
theorem iAct_adv_timeout (hXu : NUPPT.inParam X = List.replicate n true)
    {L s cur L' c O' m : List Bool}
    (hm : iAdvMove A dα din advIn (pairEncode X (iSt [] L s [] cur L' c O')) = pairEncode [false] m)
        :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [] L s [] cur L' c O')) =
      pairEncode [false] (iSt [false] L s [] (List.replicate (dα.eval n) false) []
        (List.replicate (finCall.eval n) true) O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_pos rfl, iAdvAct_eq, hm, pairFstD_pairEncode,
    if_neg (by decide)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gO_iSt, hXu,
    List.length_replicate, if_true]

/-- **The adversary queries within budget:** a call opens with `cur = m` (the query `⟨1^i, x⟩`),
an empty outer log and budget `perCall(n)`. -/
theorem iAct_adv_query (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA cur L' c O' m : List Bool}
    (hm : iAdvMove A dα din advIn (pairEncode X (iSt [] L s (true :: bA) cur L' c O')) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [] L s (true :: bA) cur L' c O')) =
      pairEncode [false] (iSt [true] L s bA m [] (List.replicate (perCall.eval n) true) O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_pos rfl, iAdvAct_eq, hm, pairFstD_pairEncode,
    if_neg (by decide), pairSndD_pairEncode, gB_iSt, if_neg (List.cons_ne_nil _ _)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gO_iSt, hXu,
    List.length_replicate, List.drop_one, List.tail_cons]

/-- The handler's move word in a call on the pending query `⟨iw, xw⟩`: the canonical decoder, with
result length `selLen dout n |iw| + stateLen(n)`, of `run ⟨ctx, ⟨s, ⟨⟨iw, xw⟩, L'⟩⟩⟩`. -/
theorem iCallMove_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA iw xw L' c O' : List Bool) :
    iCallMove dout din' stateLen run (pairEncode X (iSt ph L s bA (pairEncode iw xw) L' c O')) =
      canonWord din' n (selLen dout n iw.length + stateLen.eval n)
        (run (pairEncode (iCtx X) (pairEncode s (pairEncode (pairEncode iw xw) L')))) := by
  rw [iCallMove_eq, iAnsLen_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gS_iSt, gCur_iSt, gLc_iSt, hXu,
    List.length_replicate]
  exact canonFun_eq din' n _ _

/-- **A call ends** with the result `W`: the entry `⟨iw, ⟨xw, y⟩⟩` is appended to the adversary's
log and the state becomes `s'`, where `W = y ‖ s'` is cut at `dout i (n)`. Both the handler's answer
and the joint default end a call this way (`iAct_call_ret`, `iAct_call_timeout`). -/
theorem iCallEnd_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA iw xw L' c O' W : List Bool) :
    iCallEnd dout (pairEncode X (iSt ph L s bA (pairEncode iw xw) L' c O')) W =
      iSt [] (L ++ pairEncode (pairEncode iw (pairEncode xw
          (W.take (selLen dout n iw.length)))) [])
        (W.drop (selLen dout n iw.length)) bA [] [] [] O' := by
  rw [iCallEnd_eq, iAnsLen_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gB_iSt, gCur_iSt, gO_iSt, hXu,
    List.length_replicate]

/-- **The handler answers:** the call ends with the answer word `W` (`iCallEnd_iSt`). -/
theorem iAct_call_ret {L s bA iw xw L' c O' W : List Bool}
    (hm : iCallMove dout din' stateLen run (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' c
        O')) =
      pairEncode [true] W) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' c O')) =
      pairEncode [false] (iCallEnd dout (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' c
          O'))
        W) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    if_pos (pairFstD_pairEncode _ _), pairSndD_pairEncode]

/-- **The handler queries at budget `0`:** the call ends with the joint all-`false` default. -/
theorem iAct_call_timeout (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA iw xw L' O' m : List Bool}
    (hm : iCallMove dout din' stateLen run (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' []
        O')) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' [] O')) =
      pairEncode [false] (iCallEnd dout (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' []
          O'))
        (List.replicate (selLen dout n iw.length + stateLen.eval n) false)) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_pos rfl, iAnsLen_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gCur_iSt, hXu, List.length_replicate]

/-- **The handler queries within budget and the replayed log is exhausted:** the machine stops,
and its move is the handler's query word. -/
theorem iAct_call_stop {L s bA iw xw L' c m : List Bool}
    (hm : iCallMove dout din' stateLen run
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) [])) = pairEncode [false]
            m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) [])) =
      pairEncode [true] (pairEncode [false] m) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_neg (List.cons_ne_nil _
        _),
    gO_iSt, if_pos rfl]

/-- **The handler queries within budget and the replayed log has an entry `e`:** `e` is appended
to the call's outer log, and the budget decreases. -/
theorem iAct_call_ask {L s bA iw xw L' c e O' m : List Bool}
    (hm : iCallMove dout din' stateLen run
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] (iSt [true] L s bA (pairEncode iw xw) (L' ++ pairEncode e []) c O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_neg (List.cons_ne_nil _
        _),
    gO_iSt, if_neg (pairEncode_ne_nil _ _), iAsk_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gCur_iSt, gLc_iSt,
    gC_iSt, gO_iSt, List.drop_one, List.tail_cons]

/-- The finalization's move word on a state word: the canonical decoder, with result length
`outLen(n)`, of `finRun ⟨ctx, ⟨s, ⟨cur, L'⟩⟩⟩`. -/
theorem iFinMove_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA cur L' c O' : List Bool) :
    iFinMove din' outLen finRun (pairEncode X (iSt ph L s bA cur L' c O')) =
      canonWord din' n (outLen.eval n)
        (finRun (pairEncode (iCtx X) (pairEncode s (pairEncode cur L')))) := by
  rw [iFinMove_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gS_iSt, gCur_iSt, gLc_iSt, hXu,
    List.length_replicate]
  exact canonFun_eq din' n _ _

/-- **The finalization outputs:** the machine stops with the output word. -/
theorem iAct_fin_ret {L s bA cur L' c O' W : List Bool}
    (hm : iFinMove din' outLen finRun (pairEncode X (iSt [false] L s bA cur L' c O')) =
      pairEncode [true] W) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' c O')) =
      pairEncode [true] (pairEncode [true] W) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    if_pos (pairFstD_pairEncode _ _)]

/-- **The finalization queries at budget `0`:** the machine stops with `⟨[true], 0^{outLen(n)}⟩`. -/
theorem iAct_fin_timeout (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA cur L' O' m : List Bool}
    (hm : iFinMove din' outLen finRun (pairEncode X (iSt [false] L s bA cur L' [] O')) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' [] O')) =
      pairEncode [true] (pairEncode [true] (List.replicate (outLen.eval n) false)) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_pos rfl,
    pairFstD_pairEncode, hXu,
    List.length_replicate]

/-- **The finalization queries within budget and the replayed log is exhausted:** the machine
stops, and its move is the finalization's query word. -/
theorem iAct_fin_stop {L s bA cur L' c m : List Bool}
    (hm : iFinMove din' outLen finRun (pairEncode X (iSt [false] L s bA cur L' (true :: c) [])) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' (true :: c) [])) =
      pairEncode [true] (pairEncode [false] m) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt,
    if_neg (List.cons_ne_nil _ _), gO_iSt, if_pos rfl]

/-- **The finalization queries within budget and the replayed log has an entry `e`:** `e` is
appended to the finalization's outer log, and the budget decreases. -/
theorem iAct_fin_ask {L s bA cur L' c e O' m : List Bool}
    (hm : iFinMove din' outLen finRun
        (pairEncode X (iSt [false] L s bA cur L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] (iSt [false] L s bA cur (L' ++ pairEncode e []) c O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt,
    if_neg (List.cons_ne_nil _ _), gO_iSt, if_neg (pairEncode_ne_nil _ _), iAsk_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gCur_iSt, gLc_iSt,
    gC_iSt, gO_iSt, List.drop_one, List.tail_cons]

end Rounds

/-! ### The state bound -/

/-- **The state bound:** a state word whose components are within their bounds at parameter
`n ≤ |X|`, and whose unreplayed log is at most `|X|` long, is within `iBound` at `|X|`. -/
theorem length_iSt_le (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' dout' : Fin k' →
    PolyExpr)
    (stateLen perCall finCall : PolyExpr) {n m : ℕ} (hn : n ≤ m) {ph L s bA cur L' c O' : List Bool}
    (hph : ph.length ≤ 1) (hL : L.length ≤ q.eval n * (entryPoly din dout).eval n)
    (hs : s.length ≤ stateLen.eval n) (hbA : bA.length ≤ q.eval n)
    (hcur : cur.length ≤ (iCurBound dα din).eval n)
    (hL' : L'.length ≤ (perCall.eval n + finCall.eval n) * (entryPoly din' dout').eval n)
    (hc : c.length ≤ perCall.eval n + finCall.eval n) (hO : O'.length ≤ m) :
    (iSt ph L s bA cur L' c O').length ≤
      (iBound q dα din dout din' stateLen perCall finCall dout').eval m := by
  have hmono := (iFixBound q dα din dout din' stateLen perCall finCall dout').eval_mono hn
  rw [iBound_eq, PolyExpr.eval_add, PolyExpr.eval_var]
  refine le_trans ?_ (Nat.add_le_add_right hmono m)
  rw [iSt_eq]
  simp only [length_pairEncode, iFixBound_eq, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_const]
  have : L'.length + c.length ≤
      (perCall.eval n + finCall.eval n) * ((entryPoly din' dout').eval n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  omega

end TCSlib.Cryptography.Games.EffFill
