/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Simulate

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine of a non-interactive handler (efficiency fill, T1)

The raw function behind `Games.exists_handlerMachine` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T1"), stated over the raw ingredients of a
handler (its lengths and its three string functions) so that it does not depend on the handler
structure of `TCSlib.Cryptography.Games.Efficiency`.

On the raw layout `X = ⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩` (`α_A` the adversary's advice, `s₀` the
initial state) the function is an activation loop (`EffFill.actLoop`) on the state
`⟨L, ⟨s, 1^t⟩⟩`: the adversary's encoded log, the handler's state and the number of answered
queries. One round runs the adversary on `⟨advIn ⟨1^n, ⟨z, ω⟩⟩, L⟩`, reads its move through the
canonical decoder, and either stops (an output, or a query when the budget `q(n)` is spent) with
`out ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`, or answers the query with `run`, decoded componentwise with the
all-`false` default (`fixLen`), and appends the entry to the log.

## Main definitions

* `EffFill.hAct`, `EffFill.hStart`, `EffFill.hRaw`: the round, the initial state and the raw
  function; `EffFill.hRounds`, `EffFill.hBound`: the round and state bounds; `EffFill.hState`: the
  state.
* `EffFill.advNext`: the next-move function of a machine adversary on an input.

## Main results

* `EffFill.hRaw_poly`: the raw function is polynomial-time.
* `EffFill.hRaw_spec`: on the layout, it returns the finalized output of the simulation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations; for example the reductions of the
  proofs of Theorems 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! Seal of the efficiency fill (s2b-efficiency): a verbatim copy of `TCSlib/Cryptography/Games/Efficiency/Handler.lean` with every foreign
non-reducible TCSlib definition its declarations use made irreducible (scan: `SealScan.lean`). -/
attribute [local irreducible] _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.zeroBits _root_.Turing.pairEncode


variable {k : ℕ}

/-- The next-move function of the machine `A` on the input `x` with coins `r`: `A`'s output on
`⟨x, encoded log⟩`, decoded by the codec. -/
def advNext {ι α : Type} {spec : OracleSpec ι} (A : NUPPT) (codec : MachineCodec spec α) (n : ℕ)
    (x : List Bool) (r : A.Coins n) (hist : QueryLog spec) : Move spec α :=
  codec.decodeMove (A.runAt n (pairEncode x (codec.encodeLog hist)) r)

/-- `advNext A codec n x r hist = codec.decodeMove (A.runAt n ⟨x, codec.encodeLog hist⟩ r)`. -/
theorem advNext_eq {ι α : Type} {spec : OracleSpec ι} (A : NUPPT) (codec : MachineCodec spec α)
    (n : ℕ) (x : List Bool) (r : A.Coins n) (hist : QueryLog spec) :
    advNext A codec n x r hist = codec.decodeMove (A.runAt n (pairEncode x (codec.encodeLog hist))
        r) :=
  rfl

/-- `A`'s computation on the input `x` is `buildComp` of `advNext` (`NUPPT.toCompOn_eq`). -/
theorem toCompOn_eq_advNext {ι α : Type} {spec : OracleSpec ι} (A : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : A.Coins n) :
    A.toCompOn codec n q x r = buildComp (advNext A codec n x r) codec.timeout q [] := by
  rw [NUPPT.toCompOn_eq]
  rfl

section Raw

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (stateLen : PolyExpr)
  (run advIn out : List Bool → List Bool)

/-- The context `⟨1^n, ⟨z, ω⟩⟩` read off the raw layout `X` (its parameter and argument). -/
def hCtx (X : List Bool) : List Bool := pairEncode (NUPPT.inParam X) (NUPPT.inArg X)

/-- `hCtx X = ⟨inParam X, inArg X⟩`. -/
theorem hCtx_eq (X : List Bool) : hCtx X = pairEncode (NUPPT.inParam X) (NUPPT.inArg X) := rfl

/-- The adversary's canonical move word in the round on `w = ⟨X, ⟨L, ⟨s, c⟩⟩⟩`. -/
def hMove (w : List Bool) : List Bool :=
  canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
      (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
        (pairEncode (advIn (hCtx (pairFstD w))) (pairFstD (pairSndD w)))
        (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w))))))

/-- The defining equation of `hMove` (the canonical decoder of `A`'s output on
`⟨advIn ctx, L⟩`). -/
theorem hMove_eq (w : List Bool) :
    hMove A dα din advIn w =
      canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
          (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
            (pairEncode (advIn (hCtx (pairFstD w))) (pairFstD (pairSndD w)))
            (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w)))))) :=
  rfl

/-- The handler's output `run ⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩` on the pending query of the round. -/
def hRes (w : List Bool) : List Bool :=
  run (pairEncode (hCtx (pairFstD w))
    (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w))))

/-- The defining equation of `hRes`. -/
theorem hRes_eq (w : List Bool) :
    hRes A dα din run advIn w =
      run (pairEncode (hCtx (pairFstD w))
        (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w)))) :=
  rfl

/-- The new state of a continuing round: the log with the answered entry appended, the new state
and the incremented counter. -/
def hNext (w : List Bool) : List Bool :=
  pairEncode
    (pairFstD (pairSndD w) ++ pairEncode (pairEncode (pairFstD (pairSndD (hMove A dα din advIn w)))
      (pairEncode (pairSndD (pairSndD (hMove A dα din advIn w)))
        (fixLen (selLen dout (NUPPT.inParam (pairFstD w)).length
          (pairFstD (pairSndD (hMove A dα din advIn w))).length)
          (pairFstD (hRes A dα din run advIn w))))) [])
    (pairEncode (fixLen (stateLen.eval (NUPPT.inParam (pairFstD w)).length)
      (pairSndD (hRes A dα din run advIn w))) (true :: pairSndD (pairSndD (pairSndD w))))

/-- The defining equation of `hNext`. -/
theorem hNext_eq (w : List Bool) :
    hNext A dα din dout stateLen run advIn w =
      pairEncode
        (pairFstD (pairSndD w) ++ pairEncode (pairEncode (pairFstD (pairSndD (hMove A dα din advIn
            w)))
          (pairEncode (pairSndD (pairSndD (hMove A dα din advIn w)))
            (fixLen (selLen dout (NUPPT.inParam (pairFstD w)).length
              (pairFstD (pairSndD (hMove A dα din advIn w))).length)
              (pairFstD (hRes A dα din run advIn w))))) [])
        (pairEncode (fixLen (stateLen.eval (NUPPT.inParam (pairFstD w)).length)
          (pairSndD (hRes A dα din run advIn w))) (true :: pairSndD (pairSndD (pairSndD w)))) :=
  rfl

/-- **One round of the handler machine** on `w = ⟨X, ⟨L, ⟨s, c⟩⟩⟩`: stop with
`out ⟨ctx, ⟨s, a⟩⟩` on an output `a`; stop with `out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩` on a query when
`q(n) ≤ |c|`; otherwise continue with `hNext`. -/
def hAct (w : List Bool) : List Bool :=
  if pairFstD (hMove A dα din advIn w) = [true] then
    pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
      (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w)))))
  else if q.eval (NUPPT.inParam (pairFstD w)).length ≤ (pairSndD (pairSndD (pairSndD w))).length
      then
    pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
      (pairEncode (pairFstD (pairSndD (pairSndD w)))
        (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false))))
  else pairEncode [false] (hNext A dα din dout stateLen run advIn w)

/-- The defining equation of `hAct`. -/
theorem hAct_eq (w : List Bool) :
    hAct A q dα din dout stateLen run advIn out w =
      if pairFstD (hMove A dα din advIn w) = [true] then
        pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
          (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w)))))
      else if q.eval (NUPPT.inParam (pairFstD w)).length ≤
          (pairSndD (pairSndD (pairSndD w))).length then
        pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
          (pairEncode (pairFstD (pairSndD (pairSndD w)))
            (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false))))
      else pairEncode [false] (hNext A dα din dout stateLen run advIn w) :=
  rfl

/-- The initial state `⟨[], ⟨s₀, []⟩⟩`, with the initial state `s₀` read off the advice. -/
def hStart (X : List Bool) : List Bool :=
  pairEncode [] (pairEncode (pairSndD (NUPPT.inAdvice X)) [])

/-- `hStart X = ⟨[], ⟨snd (inAdvice X), []⟩⟩`. -/
theorem hStart_eq (X : List Bool) :
    hStart X = pairEncode [] (pairEncode (pairSndD (NUPPT.inAdvice X)) []) := rfl

/-- The round bound `q + 1`: at most `q(n)` answered queries and one stopping round. -/
def hRounds : PolyExpr := .add q (.const 1)

/-- `hRounds q = q + 1`. -/
theorem hRounds_eq : hRounds q = .add q (.const 1) := rfl

/-- The state bound `2 q E + 2 stateLen + q + 4` (`E` the entry bound `entryPoly`). -/
def hBound : PolyExpr :=
  .add (.mul (.const 2) (.mul q (entryPoly din dout))) (.add (.mul (.const 2) stateLen) (.add q
      (.const 4)))

/-- The defining equation of `hBound`. -/
theorem hBound_eq : hBound q din dout stateLen =
    .add (.mul (.const 2) (.mul q (entryPoly din dout))) (.add (.mul (.const 2) stateLen) (.add q
        (.const 4))) :=
  rfl

/-- **The raw function of the handler machine:** the activation loop of `hAct` from `hStart`, with
`q + 1` rounds and the state bound `hBound`. -/
def hRaw : List Bool → List Bool :=
  actLoop hStart (hAct A q dα din dout stateLen run advIn out) (hRounds q) (hBound q din dout
      stateLen)

/-- `hRaw = actLoop hStart hAct (q + 1) hBound`. -/
theorem hRaw_eq : hRaw A q dα din dout stateLen run advIn out =
    actLoop hStart (hAct A q dα din dout stateLen run advIn out) (hRounds q)
      (hBound q din dout stateLen) :=
  rfl

/-! ### Polynomial time -/

variable {run advIn out}

/-- The context is polynomial-time. -/
theorem hCtx_poly : PolyTimeComputable hCtx :=
  NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg

/-- The round's move is polynomial-time. -/
theorem hMove_poly (hadvIn : PolyTimeComputable advIn) : PolyTimeComputable (hMove A dα din advIn)
    := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hout := A.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    ((hadvIn.comp' (hCtx_poly.comp' hX)).pairEncode
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD))
    (polyTimeComputable_pairFstD.comp' (NUPPT.polyTimeComputable_inAdvice.comp' hX))
    (NUPPT.polyTimeComputable_inCoins.comp' hX))
  exact (canonFun_poly din).comp' (hu.pairEncode ((StateLoop.unaryPoly_comp dα hu).pairEncode hout))

/-- The handler's output on the pending query is polynomial-time. -/
theorem hRes_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (hRes A dα din run advIn) :=
  hrun.comp' ((hCtx_poly.comp' polyTimeComputable_pairFstD).pairEncode
    ((polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
      polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_pairSndD.comp' (hMove_poly A dα din hadvIn))))

/-- The continuing state is polynomial-time. -/
theorem hNext_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (hNext A dα din dout stateLen run advIn) := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hm := hMove_poly A dα din hadvIn
  have hq := polyTimeComputable_pairSndD.comp' hm
  have hres := hRes_poly A dα din hrun hadvIn
  have hy := fixLen_poly ((selLen_poly dout).comp' (hu.pairEncode (polyTimeComputable_pairFstD.comp'
      hq)))
    (polyTimeComputable_pairFstD.comp' hres)
  have hs := fixLen_poly (StateLoop.unaryPoly_comp stateLen hu) (polyTimeComputable_pairSndD.comp'
      hres)
  have h := ((polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).append
    (((polyTimeComputable_pairFstD.comp' hq).pairEncode
      ((polyTimeComputable_pairSndD.comp' hq).pairEncode hy)).pairEncode
        (polyTimeComputable_const []))).pairEncode
    (hs.pairEncode ((StateLoop.cons_poly true).comp' (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD))))
  refine h.congr fun w => ?_
  rw [hNext_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **One round of the handler machine is polynomial-time.** -/
theorem hAct_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn)
    (hout : PolyTimeComputable out) : PolyTimeComputable (hAct A q dα din dout stateLen run advIn
        out) := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hm := hMove_poly A dα din hadvIn
  have hctx := hCtx_poly.comp' hX
  have hst := polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    polyTimeComputable_pairSndD)
  have hc := polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
    polyTimeComputable_pairSndD)
  have h1 := eq_poly (polyTimeComputable_pairFstD.comp' hm) (polyTimeComputable_const [true])
  have h2 := StateLoop.lenLe_comp hc (StateLoop.unaryPoly_comp q hu)
  have hz : PolyTimeComputable fun w =>
      List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false :=
    (zeros_poly (StateLoop.unaryPoly_comp dα hu)).congr fun w => by rw [List.length_replicate]
  have h := polyTimeComputable_ite h1
    ((polyTimeComputable_const [true]).pairEncode (hout.comp' (hctx.pairEncode
      (hst.pairEncode (polyTimeComputable_pairSndD.comp' hm)))))
    (polyTimeComputable_ite h2
      ((polyTimeComputable_const [true]).pairEncode (hout.comp' (hctx.pairEncode (hst.pairEncode
          hz))))
      ((polyTimeComputable_const [false]).pairEncode (hNext_poly A dα din dout stateLen hrun
          hadvIn)))
  refine h.congr fun w => ?_
  rw [hAct_eq]
  simp only [List.length_replicate, decide_eq_true_eq]

/-- **The raw function of the handler machine is polynomial-time** (`actLoop_poly`). -/
theorem hRaw_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn)
    (hout : PolyTimeComputable out) : PolyTimeComputable (hRaw A q dα din dout stateLen run advIn
        out) :=
  actLoop_poly ((polyTimeComputable_const []).pairEncode
      ((polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inAdvice).pairEncode
        (polyTimeComputable_const [])))
    (hAct_poly A q dα din dout stateLen hrun hadvIn hout) _ _

end Raw

/-! ### The functional equation -/

section Spec

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (stateLen : PolyExpr)
  (run advIn out : List Bool → List Bool)

/-- The state `⟨L, ⟨s, 1^t⟩⟩` of the handler machine: the encoded log, the handler's state and
the number `t` of answered queries. -/
def hState (L s : List Bool) (t : ℕ) : List Bool :=
  pairEncode L (pairEncode s (List.replicate t true))

/-- `hState L s t = ⟨L, ⟨s, 1^t⟩⟩`. -/
theorem hState_eq (L s : List Bool) (t : ℕ) :
    hState L s t = pairEncode L (pairEncode s (List.replicate t true)) :=
  rfl

/-- The move word of a round on the state `⟨L, ⟨s, 1^t⟩⟩` at parameter `n`: the canonical decoder
of `A`'s output on `⟨advIn ctx, L⟩` with the advice and coins of the layout. -/
theorem hMove_state {X : List Bool} {n : ℕ} (hXu : NUPPT.inParam X = List.replicate n true)
    (L s : List Bool) (t : ℕ) :
    hMove A dα din advIn (pairEncode X (hState L s t)) =
      canonWord din n (dα.eval n) (A.output (NUPPT.layout (List.replicate n true)
        (pairEncode (advIn (hCtx X)) L) (pairFstD (NUPPT.inAdvice X)) (NUPPT.inCoins X))) := by
  rw [hMove_eq, hState_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hXu, List.length_replicate]
  exact canonFun_eq din n (dα.eval n) _

/-- **A round on an output stops:** if the move word is `⟨[true], a⟩`, the round stops with
`out ⟨ctx, ⟨s, a⟩⟩`. -/
theorem hAct_of_ret {X : List Bool} {L s a : List Bool} {t : ℕ}
    (hm : hMove A dα din advIn (pairEncode X (hState L s t)) = pairEncode [true] a) :
    hAct A q dα din dout stateLen run advIn out (pairEncode X (hState L s t)) =
      pairEncode [true] (out (pairEncode (hCtx X) (pairEncode s a))) := by
  rw [hAct_eq, hm, if_pos (pairFstD_pairEncode _ _)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hState_eq]

/-- **A query with the budget spent stops:** if the move word is a query `⟨[false], m⟩` and
`q(n) ≤ t`, the round stops with `out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩`. -/
theorem hAct_of_timeout {X : List Bool} {n : ℕ} (hXu : NUPPT.inParam X = List.replicate n true)
    {L s m : List Bool} {t : ℕ}
    (hm : hMove A dα din advIn (pairEncode X (hState L s t)) = pairEncode [false] m)
    (ht : q.eval n ≤ t) :
    hAct A q dα din dout stateLen run advIn out (pairEncode X (hState L s t)) =
      pairEncode [true] (out (pairEncode (hCtx X) (pairEncode s
        (List.replicate (dα.eval n) false)))) := by
  have hne : pairFstD (pairEncode [false] m) ≠ [true] := by
    rw [pairFstD_pairEncode]
    decide
  rw [hAct_eq, hm, if_neg hne]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hState_eq, hXu, List.length_replicate]
  rw [if_pos ht]

/-- **A query within budget continues:** if the move word is the query `⟨[false], ⟨iw, xw⟩⟩` and
`t < q(n)`, the round continues with the entry `⟨iw, ⟨xw, y⟩⟩` appended to the log, the new state
`s'` and `t + 1`, where `y` and `s'` are `run ⟨ctx, ⟨s, ⟨iw, xw⟩⟩⟩` decoded componentwise. -/
theorem hAct_of_query {X : List Bool} {n : ℕ} (hXu : NUPPT.inParam X = List.replicate n true)
    {L s iw xw : List Bool} {t : ℕ}
    (hm : hMove A dα din advIn (pairEncode X (hState L s t)) =
      pairEncode [false] (pairEncode iw xw))
    (ht : t < q.eval n) :
    hAct A q dα din dout stateLen run advIn out (pairEncode X (hState L s t)) =
      pairEncode [false] (hState
        (L ++ pairEncode (pairEncode iw (pairEncode xw (fixLen (selLen dout n iw.length)
          (pairFstD (run (pairEncode (hCtx X) (pairEncode s (pairEncode iw xw)))))))) [])
        (fixLen (stateLen.eval n) (pairSndD (run (pairEncode (hCtx X) (pairEncode s
          (pairEncode iw xw)))))) (t + 1)) := by
  have hne : pairFstD (pairEncode [false] (pairEncode iw xw)) ≠ [true] := by
    rw [pairFstD_pairEncode]
    decide
  rw [hAct_eq, hm, if_neg hne, hNext_eq, hRes_eq, hm]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hState_eq, hXu, List.length_replicate]
  rw [if_neg (Nat.not_le.2 ht), List.replicate_succ]

/-- **The functional equation of the handler machine.** At parameter `n`, on the layout
`X = ⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩` with `α_A = A.advice n`, for any answer function `ans`
that agrees with `run` decoded componentwise (`fixLen`), the simulation of `A` on
`advIn ⟨1^n, ⟨z, ω⟩⟩` with the stateless answers `ans` from `s₀` returns some `(a, s)`, and the
raw function returns `out ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`.

**Proof sketch.** By induction on the remaining budget `b`, from the round `t = q(n) − b` whose
state is `⟨encodeLog hist, ⟨s, 1^t⟩⟩` (`RunsTo`). The round's move word is the canonical word of
`A`'s next move (`hMove_state`, `canonWord_eq`, `NUPPT.runAtL_eq_output_layout`). On an output `a`
the round stops with `out ⟨ctx, ⟨s, a⟩⟩` (`hAct_of_ret`) and `buildComp` returns `a`
(`buildComp_zero_of_ret`, `buildComp_succ_of_ret`, `simulate_pure`). On a query with `b = 0` it
stops with the all-`false` output (`hAct_of_timeout`), as `buildComp_zero_of_query` does. On a
query with `b > 0` the round continues (`hAct_of_query`) with the answered entry appended
(`encodeLog_append_single`, `bitCodec_encodeEntry`) and the new state, which is the state of
`simulate` after `buildComp_succ_of_query`, `simulate_query` and `pure_bind`. The states stay
within `hBound` (`length_encodeLog_le`, `entry_le_entryPoly`, `PolyExpr.eval_mono`), and the
stopping
round is at most `q(n) ≤ (q + 1)(|X|)`; `runsTo_stop` evaluates the loop. -/
theorem hRaw_spec {ι' : Type} {spec' : OracleSpec ι'} (n : ℕ) (z ω : List Bool) (r : A.Coins n)
    (init : Fin (stateLen.eval n) → Bool)
    (ans : ∀ i : Fin k, (Fin ((din i).eval n) → Bool) → (Fin (stateLen.eval n) → Bool) →
      (Fin ((dout i).eval n) → Bool) × (Fin (stateLen.eval n) → Bool))
    (hans : ∀ i x s,
      List.ofFn (ans i x s).1 = fixLen ((dout i).eval n) (pairFstD (run (pairEncode
        (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) ∧
      List.ofFn (ans i x s).2 = fixLen (stateLen.eval n) (pairSndD (run (pairEncode
        (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x))))))) :
    ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (stateLen.eval n) → Bool),
      simulate (spec' := spec') (fun i x s => OracleComp.pure (ans i x s))
          (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
            n (q.eval n) (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) init =
        .pure (a, s) ∧
      hRaw A q dα din dout stateLen run advIn out
          (NUPPT.layout (List.replicate n true) (pairEncode z ω)
            (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r)) =
        out (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
          (pairEncode (List.ofFn s) (List.ofFn a))) := by
  -- The fixed data of the run.
  set X := NUPPT.layout (List.replicate n true) (pairEncode z ω)
    (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r) with hX
  set ctx := pairEncode (List.replicate n true) (pairEncode z ω) with hctx
  set codec := bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)
    with hcodec
  have hnX : n ≤ X.length := le_length_layout n _ _ _
  have hXu : NUPPT.inParam X = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hXctx : hCtx X = ctx := by rw [hCtx_eq, hXu, hX, NUPPT.inArg_layout]
  -- The move word of a round is the canonical word of `A`'s next move.
  have hmove : ∀ (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
      (s : Fin (stateLen.eval n) → Bool) (t : ℕ), hMove A dα din advIn
      (pairEncode X (hState (codec.encodeLog hist) (List.ofFn s) t)) =
      encodeBitMove (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)
        (advNext A codec n (advIn ctx) r hist) := by
    intro hist s t
    rw [hMove_state A dα din advIn hXu, hXctx, hX, NUPPT.inAdvice_layout, NUPPT.inCoins_layout,
      pairFstD_pairEncode, ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq,
      canonWord_eq din (fun i => (dout i).eval n), advNext_eq, hcodec, bitCodec_decodeMove]
  -- The state bound.
  have hbound : ∀ (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
      (s : Fin (stateLen.eval n) → Bool) (t : ℕ), hist.length = t → t ≤ q.eval n →
      (hState (codec.encodeLog hist) (List.ofFn s) t).length ≤
        (hBound q din dout stateLen).eval X.length := by
    intro hist s t hlen ht
    have hlog := length_encodeLog_le codec ((entryPoly din dout).eval n) hist
      (fun e _ => entry_le_entryPoly din dout n e (dα.eval n))
    refine le_trans ?_ ((hBound q din dout stateLen).eval_mono hnX)
    rw [hState_eq, length_pairEncode, length_pairEncode, List.length_ofFn, List.length_replicate,
      hBound_eq]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    rw [hlen] at hlog
    have : t * (entryPoly din dout).eval n ≤ q.eval n * (entryPoly din dout).eval n :=
      Nat.mul_le_mul_right _ ht
    omega
  have hR : ∀ t, t ≤ q.eval n → t ≤ (hRounds q).eval X.length := by
    intro t ht
    rw [hRounds_eq, PolyExpr.eval_add, PolyExpr.eval_const]
    have := q.eval_mono hnX
    omega
  -- The induction on the remaining budget.
  have key : ∀ b hist (s : Fin (stateLen.eval n) → Bool) t, t + b = q.eval n →
      hist.length = t →
      RunsTo hStart (hAct A q dα din dout stateLen run advIn out) (hBound q din dout stateLen) X t
        (hState (codec.encodeLog hist) (List.ofFn s) t) →
      ∃ (a : Fin (dα.eval n) → Bool) (s' : Fin (stateLen.eval n) → Bool),
        simulate (spec' := spec') (fun i x s => OracleComp.pure (ans i x s))
            (buildComp (advNext A codec n (advIn ctx) r) codec.timeout b hist) s = .pure (a, s') ∧
        hRaw A q dα din dout stateLen run advIn out X =
          out (pairEncode ctx (pairEncode (List.ofFn s') (List.ofFn a))) := by
    intro b
    induction b with
    | zero =>
      intro hist s t ht hlen hrun
      cases hm : advNext A codec n (advIn ctx) r hist with
      | ret a =>
        refine ⟨a, s, by rw [buildComp_zero_of_ret hm, simulate_pure], ?_⟩
        refine runsTo_stop hrun ?_ (hR t (by omega))
        rw [hAct_of_ret A q dα din dout stateLen run advIn out
          (by rw [hmove, hm, encodeBitMove_ret]), hXctx]
      | query i x =>
        refine ⟨zeroBits _, s, ?_, ?_⟩
        · rw [buildComp_zero_of_query hm, simulate_pure, hcodec, bitCodec_timeout]
        · refine runsTo_stop hrun ?_ (hR t (by omega))
          rw [hAct_of_timeout A q dα din dout stateLen run advIn out hXu
            (by rw [hmove, hm, encodeBitMove_query]) (by omega), hXctx, ofFn_zeroBits]
    | succ b ih =>
      intro hist s t ht hlen hrun
      cases hm : advNext A codec n (advIn ctx) r hist with
      | ret a =>
        refine ⟨a, s, by rw [buildComp_succ_of_ret hm, simulate_pure], ?_⟩
        refine runsTo_stop hrun ?_ (hR t (by omega))
        rw [hAct_of_ret A q dα din dout stateLen run advIn out
          (by rw [hmove, hm, encodeBitMove_ret]), hXctx]
      | query i x =>
        have hlen' : (hist ++ [(⟨i, x, (ans i x s).1⟩ : Σ i, (bitSpec (fun i => (din i).eval n)
            (fun i => (dout i).eval n)).dom i × (bitSpec (fun i => (din i).eval n)
            (fun i => (dout i).eval n)).rng i)]).length = t + 1 := by
          rw [List.length_append, hlen, List.length_singleton]
        have hnext : hAct A q dα din dout stateLen run advIn out
            (pairEncode X (hState (codec.encodeLog hist) (List.ofFn s) t)) =
            pairEncode [false] (hState (codec.encodeLog (hist ++ [⟨i, x, (ans i x s).1⟩]))
              (List.ofFn (ans i x s).2) (t + 1)) := by
          rw [hAct_of_query A q dα din dout stateLen run advIn out hXu
            (by rw [hmove, hm, encodeBitMove_query]) (by omega), hXctx, List.length_replicate,
            selLen_eq, ← (hans i x s).1, ← (hans i x s).2, encodeLog_append_single, hcodec,
            bitCodec_encodeEntry]
        obtain ⟨a, s', hsim, hraw⟩ := ih (hist ++ [⟨i, x, (ans i x s).1⟩]) (ans i x s).2 (t + 1)
          (by omega) hlen' (runsTo_succ hrun hnext (hbound _ _ _ hlen' (by omega)))
        refine ⟨a, s', ?_, hraw⟩
        rw [buildComp_succ_of_query hm, simulate_query, OracleComp.pure_bind]
        exact hsim
  have hstart : hStart X = hState (codec.encodeLog []) (List.ofFn init) 0 := by
    rw [hStart_eq, hX, NUPPT.inAdvice_layout, pairSndD_pairEncode, hState_eq,
      MachineCodec.encodeLog_nil, List.replicate_zero]
  have h0 : RunsTo hStart (hAct A q dα din dout stateLen run advIn out) (hBound q din dout stateLen)
      X 0 (hState (codec.encodeLog []) (List.ofFn init) 0) := by
    rw [← hstart]
    exact runsTo_zero (by rw [hstart]; exact hbound [] init 0 rfl (Nat.zero_le _))
  obtain ⟨a, s, hsim, hraw⟩ := key (q.eval n) [] init 0 (Nat.zero_add _) rfl h0
  refine ⟨a, s, ?_, hraw⟩
  rw [toCompOn_eq_advNext]
  exact hsim

end Spec

end TCSlib.Cryptography.Games.EffFill
