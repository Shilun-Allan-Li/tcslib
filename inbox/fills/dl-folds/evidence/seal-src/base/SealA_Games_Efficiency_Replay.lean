/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replaying a computation with a next-move function (efficiency fill, S3)

A next-move function `f` (of the log so far) **replays** an oracle computation `t` when `f []` is
`t`'s first move and, at a query, `f` extended by the query and any answer replays the
continuation (`ReplaysFrom`). If it does and `t` makes at most `b` queries, then `buildComp` of `f`
with budget `b` is `t` itself (`buildComp_of_replaysFrom`): the budget never cuts the replay
short. The interactive efficiency target (`Games.exists_interactiveHandlerMachine`) uses it, with
the cost scaling lemma `costBoundedBy_mul` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"Shared pieces", S3, and §"T2", step 4).

## Main definitions

* `EffFill.ReplaysFrom t f`: the next-move function `f` replays `t`.

## Main results

* `EffFill.buildComp_of_replaysFrom`: a replay within budget builds the computation.
* `EffFill.costBoundedBy_mul`: charging `p` per query multiplies a query bound by `p`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

/-! Seal A (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Games/Efficiency/Replay.lean`, with every seal candidate of its
full TCSlib import closure (202 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.TimeConstructible _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


variable {ι α : Type} {spec : OracleSpec ι}

/-- **`f` replays `t`:** at a return `a`, `f []` is the output `a`; at a query `x` to oracle `i`
with continuation `k`, `f []` is that query and, for every answer `y`, the function
`O ↦ f (⟨i, x, y⟩ :: O)` replays `k y`. (The argument of `f` is the log after the current
position.) -/
def ReplaysFrom : OracleComp spec α → (QueryLog spec → Move spec α) → Prop
  | .pure a, f => f [] = .ret a
  | .query i x k, f => f [] = .query i x ∧ ∀ y, ReplaysFrom (k y) fun O => f (⟨i, x, y⟩ :: O)

/-- A return is replayed when the function outputs it: `ReplaysFrom (pure a) f ↔ f [] = ret a`. -/
theorem replaysFrom_pure_iff (a : α) (f : QueryLog spec → Move spec α) :
    ReplaysFrom (.pure a) f ↔ f [] = .ret a :=
  Iff.rfl

/-- A query is replayed when the function asks it and replays every continuation:
`ReplaysFrom (query i x k) f ↔ f [] = query i x ∧ ∀ y, ReplaysFrom (k y) (f ∘ (⟨i, x, y⟩ :: ·))`. -/
theorem replaysFrom_query_iff (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : QueryLog spec → Move spec α) :
    ReplaysFrom (.query i x k) f ↔
      f [] = .query i x ∧ ∀ y, ReplaysFrom (k y) fun O => f (⟨i, x, y⟩ :: O) :=
  Iff.rfl

/-- **A replay within budget builds the computation.** If `O ↦ next (hist ++ O)` replays `t` and
`t` makes at most `b` queries, then `buildComp next timeout b hist = t`.

**Proof sketch.** Induction on `t`, generalizing the log and the budget. A return `a` is
`next hist = ret a`, and `buildComp` returns `a` at every budget (`buildComp_zero_of_ret`,
`buildComp_succ_of_ret`). A query costs `1 ≤ b`, so `b = b' + 1`, and `buildComp` asks the same
query (`buildComp_succ_of_query`); each continuation is replayed from `hist ++ [⟨i, x, y⟩]`
(`List.append_assoc`) within `b'`, and agrees by induction. -/
theorem buildComp_of_replaysFrom (next : QueryLog spec → Move spec α) (timeout : α) :
    ∀ (t : OracleComp spec α) (hist : QueryLog spec) (b : ℕ),
      ReplaysFrom t (fun O => next (hist ++ O)) → t.CostBoundedBy (fun _ => 1) b →
        buildComp next timeout b hist = t := by
  intro t
  induction t with
  | pure a =>
    intro hist b h _
    have h' : next hist = .ret a := by
      have := (replaysFrom_pure_iff a _).1 h
      rwa [List.append_nil] at this
    cases b with
    | zero => exact buildComp_zero_of_ret h'
    | succ b => exact buildComp_succ_of_ret h'
  | query i x k ih =>
    intro hist b h hc
    obtain ⟨h1, h2⟩ := (replaysFrom_query_iff i x k _).1 h
    rw [List.append_nil] at h1
    obtain ⟨hb, hk⟩ := (OracleComp.costBoundedBy_query _ i x k b).1 hc
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [buildComp_succ_of_query h1]
    refine congrArg (OracleComp.query i x) (funext fun y => ih y _ b ?_ ?_)
    · have e : (fun O => next ((hist ++ [⟨i, x, y⟩]) ++ O)) =
          fun O => next (hist ++ ⟨i, x, y⟩ :: O) := by
        funext O
        rw [List.append_assoc, List.singleton_append]
      rw [e]
      exact h2 y
    · have := hk y
      rwa [Nat.add_sub_cancel] at this

/-- **Charging `p` per query multiplies the bound by `p`:** a computation with at most `q` queries
is cost-bounded by `q · p` when every query costs `p`.

**Proof sketch.** Induction on the computation: a query needs `1 ≤ q`, so `p ≤ q · p`, and the
continuation's bound `(q − 1) · p` is `q · p − p` (`Nat.sub_one_mul`). -/
theorem costBoundedBy_mul {c : OracleComp spec α} {q : ℕ}
    (h : c.CostBoundedBy (fun _ => 1) q) (p : ℕ) : c.CostBoundedBy (fun _ => p) (q * p) := by
  induction c generalizing q with
  | pure a => exact OracleComp.costBoundedBy_pure _ _ _
  | query i x k ih =>
    obtain ⟨hq, hk⟩ := (OracleComp.costBoundedBy_query _ i x k q).1 h
    refine (OracleComp.costBoundedBy_query _ i x k _).2 ⟨?_, fun y => ?_⟩
    · exact Nat.le_mul_of_pos_left p hq
    · rw [← Nat.sub_one_mul]
      exact ih y (hk y)

end TCSlib.Cryptography.Games.EffFill
