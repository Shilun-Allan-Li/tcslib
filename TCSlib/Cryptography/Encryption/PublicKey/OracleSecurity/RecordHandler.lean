/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The recording handler of a single-challenge reduction

A reduction from CPA security to an indistinguishability assumption with one challenge
[PS10, the claim after Definition 171.5] runs the adversary once. It answers every decryption
query with `⊥` and every challenge query with the same string, its own challenge, and it
records the first challenge query `⟨m₀, m₁⟩` (two bits) to post-process the adversary's
output. This file builds that handler as a `Games.PolyHandler` (`recHandler`), generic in the
ciphertext-length polynomial and in the polynomial-time function `ans` that computes the
challenge answer from the reduction's context, so that T1 (`Games.exists_handlerMachine`) makes
it a machine.

Its simulation is the deterministic run `ChallengeSim.chRun` with the constant challenge answer
`ans ctx`, and its final state records `ChallengeSim.firstQ` (`simulate_recHandler_init`).

## Main definitions

* `ChallengeSim.recDin`, `recDout`: the query and answer lengths of the two oracles.
* `ChallengeSim.recRun`, `recOut`: the handler's step and finalization as string functions.
* `ChallengeSim.recHandler Lc ans hans`: the handler.

## Main results

* `ChallengeSim.simulate_recHandler_recorded`, `simulate_recHandler_init`: the handler's
  simulation is the deterministic run with the constant answer, and its final state records the
  first challenge query.
* `ChallengeSim.recOut_init`, `recOut_recorded`: the finalization's output bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability.ChallengeSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Lengths -/

/-- The query lengths: `Lc(n)`-bit ciphertexts to oracle `0` (decryption), two-bit challenge
queries `⟨m₀, m₁⟩` to oracle `1`. -/
def recDin (Lc : PolyExpr) : Fin 2 → PolyExpr
  | 0 => Lc
  | 1 => .const 2

/-- Decryption queries have `Lc(n)` bits. -/
theorem recDin_zero (Lc : PolyExpr) : recDin Lc 0 = Lc := rfl

/-- Challenge queries have two bits. -/
theorem recDin_one (Lc : PolyExpr) : recDin Lc 1 = .const 2 := rfl

/-- The answer lengths: a two-bit decryption answer (a validity flag and one message bit) and an
`Lc(n)`-bit challenge ciphertext. -/
def recDout (Lc : PolyExpr) : Fin 2 → PolyExpr
  | 0 => .const 2
  | 1 => Lc

/-- Decryption answers have two bits. -/
theorem recDout_zero (Lc : PolyExpr) : recDout Lc 0 = .const 2 := rfl

/-- Challenge answers have `Lc(n)` bits. -/
theorem recDout_one (Lc : PolyExpr) : recDout Lc 1 = Lc := rfl

/-! ### The step function -/

/-- **One step of the recording handler** on `⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩`. A challenge query (`i = 1`)
is answered with `ans ctx`; if the state's first bit is unset, the new state is `1 :: x` (the
query recorded), otherwise the state is kept. A decryption query (`i = 0`) is answered `00` and
keeps the state. -/
def recRun (ans : List Bool → List Bool) (w : List Bool) : List Bool :=
  if (pairFstD (pairSndD (pairSndD w))).headD false then
    pairEncode (ans (pairFstD w))
      (if (pairFstD (pairSndD w)).headD false then pairFstD (pairSndD w)
        else true :: pairSndD (pairSndD (pairSndD w)))
  else pairEncode [false, false] (pairFstD (pairSndD w))

/-- The defining equation of `recRun`. -/
theorem recRun_eq (ans : List Bool → List Bool) (w : List Bool) :
    recRun ans w =
      if (pairFstD (pairSndD (pairSndD w))).headD false then
        pairEncode (ans (pairFstD w))
          (if (pairFstD (pairSndD w)).headD false then pairFstD (pairSndD w)
            else true :: pairSndD (pairSndD (pairSndD w)))
      else pairEncode [false, false] (pairFstD (pairSndD w)) := rfl

/-- A decryption query is answered `00` and keeps the state. -/
theorem recRun_dec (ans : List Bool → List Bool) (ctx s x : List Bool) :
    recRun ans (pairEncode ctx (pairEncode s (pairEncode [] x))) =
      pairEncode [false, false] s := by
  simp only [recRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_nil,
    Bool.false_eq_true, if_false]

/-- The first challenge query `x` (state's first bit unset) is answered with `ans ctx` and
recorded as the state `1 :: x`. -/
theorem recRun_fresh (ans : List Bool → List Bool) (ctx s x : List Bool)
    (hs : s.headD false = false) :
    recRun ans (pairEncode ctx (pairEncode s (pairEncode [true] x))) =
      pairEncode (ans ctx) (true :: x) := by
  simp only [recRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true, hs,
    Bool.false_eq_true, if_false]

/-- A later challenge query (state's first bit set) is answered with `ans ctx` and keeps the
state. -/
theorem recRun_recorded (ans : List Bool → List Bool) (ctx s x : List Bool)
    (hs : s.headD false = true) :
    recRun ans (pairEncode ctx (pairEncode s (pairEncode [true] x))) = pairEncode (ans ctx) s := by
  simp only [recRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true, hs]

/-- The step function is polynomial-time when `ans` is. -/
theorem polyTimeComputable_recRun {ans : List Bool → List Bool} (hans : PolyTimeComputable ans) :
    PolyTimeComputable (recRun ans) := by
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hq : PolyTimeComputable fun w => [(pairFstD (pairSndD (pairSndD w))).headD false] :=
    polyTimeComputable_headD.comp
      (polyTimeComputable_pairFstD.comp
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hh : PolyTimeComputable fun w => [(pairFstD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp hs
  have hx : PolyTimeComputable fun w => true :: pairSndD (pairSndD (pairSndD w)) :=
    (polyTimeComputable_const [true]).append (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  exact polyTimeComputable_ite hq
    ((hans.comp polyTimeComputable_pairFstD).pairEncode (polyTimeComputable_ite hh hs hx))
    ((polyTimeComputable_const [false, false]).pairEncode hs)

/-! ### The finalization -/

/-- **The finalization** on `⟨ctx, ⟨s, a⟩⟩`, with `s = [asked, m₀, m₁]` and `a` the adversary's
bit: `[a]` if `(m₀, m₁) = (0, 1)`, `[¬a]` if `(m₀, m₁) = (1, 0)`, and `[0]` if `m₀ = m₁` or no
challenge was asked. -/
def recOut (w : List Bool) : List Bool :=
  if (pairFstD (pairSndD w)).headD false then
    if ((pairFstD (pairSndD w)).drop 1).headD false then
      if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then [false]
      else [!(pairSndD (pairSndD w)).headD false]
    else
      if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then
        [(pairSndD (pairSndD w)).headD false]
      else [false]
  else [false]

/-- The defining equation of `recOut`. -/
theorem recOut_eq (w : List Bool) :
    recOut w =
      if (pairFstD (pairSndD w)).headD false then
        if ((pairFstD (pairSndD w)).drop 1).headD false then
          if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then [false]
          else [!(pairSndD (pairSndD w)).headD false]
        else
          if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then
            [(pairSndD (pairSndD w)).headD false]
          else [false]
      else [false] := rfl

/-- Without a recorded challenge the finalization outputs `[0]`. -/
theorem recOut_init (ctx a : List Bool) :
    recOut (pairEncode ctx (pairEncode [false, false, false] a)) = [false] := by
  simp only [recOut_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    Bool.false_eq_true, if_false]

/-- With the challenge `(m₀, m₁)` recorded, the finalization outputs the bit
`(m₀ ≠ m₁) ∧ (a ≠ m₀)`: `a` for `(0, 1)`, `¬a` for `(1, 0)`, and `0` otherwise. -/
theorem recOut_recorded (ctx a : List Bool) (m₀ m₁ : Bool) :
    recOut (pairEncode ctx (pairEncode [true, m₀, m₁] a)) =
      [(m₀ != m₁) && (a.headD false != m₀)] := by
  simp only [recOut_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true,
    List.drop_succ_cons, List.drop_zero]
  cases m₀ <;> cases m₁ <;> cases a.headD false <;> rfl

/-- The finalization is polynomial-time. -/
theorem polyTimeComputable_recOut : PolyTimeComputable recOut := by
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hs₁ : PolyTimeComputable fun w => (pairFstD (pairSndD w)).drop 1 :=
    polyTimeComputable_tail.comp hs
  have hs₂ : PolyTimeComputable fun w => ((pairFstD (pairSndD w)).drop 1).drop 1 :=
    polyTimeComputable_tail.comp hs₁
  have ha : PolyTimeComputable fun w => [(pairSndD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hs)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp hs₁)
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hs₂) (polyTimeComputable_const _)
        (polyTimeComputable_not ha))
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hs₂) ha (polyTimeComputable_const _)))
    (polyTimeComputable_const _)

/-! ### The handler -/

/-- The adversary's input: the first component `pk` of the reduction input `z = ⟨pk, c⟩`, read
from the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def recAdvIn (ctx : List Bool) : List Bool := pairFstD (pairFstD (pairSndD ctx))

/-- The defining equation of `recAdvIn`. -/
theorem recAdvIn_eq (ctx : List Bool) : recAdvIn ctx = pairFstD (pairFstD (pairSndD ctx)) := rfl

/-- **The recording handler** with ciphertext length `Lc` and challenge answer `ans ctx`: three
state bits `[asked, m₀, m₁]`, initially `000`; no seed; the adversary runs on `pk`, the first
component of the reduction input; decryption queries are answered `00`; challenge queries are
answered `ans ctx`, and the first one is recorded; the output is `recOut`. -/
noncomputable def recHandler (Lc : PolyExpr) (ans : List Bool → List Bool)
    (hans : PolyTimeComputable ans) : PolyHandler 2 (recDin Lc) (recDout Lc) where
  stateLen := .const 3
  seedLen := .const 0
  init _ := zeroBits _
  run := recRun ans
  poly := polyTimeComputable_recRun hans
  advIn := recAdvIn
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  out := recOut
  out_poly := polyTimeComputable_recOut

attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out] recHandler

/-! ### The handler's simulation -/

section Simulation

variable {α : Type} (Lc : PolyExpr) {ans : List Bool → List Bool} (hans : PolyTimeComputable ans)
  (n : ℕ) (z : List Bool) (ω : Fin ((recHandler Lc ans hans).seedLen.eval n) → Bool)

/-- **After the challenge is recorded**, the handler's simulation is the deterministic run with
the constant challenge answer `w = ans ⟨1^n, ⟨z, ω⟩⟩` from the recorded state `padFin w`, and the
handler's state does not change. Requires `|w| = Lc(n)`.

**Proof sketch.** Induction on the computation. A decryption query is answered `00`
(`recRun_dec`), the all-`false` answer of `chRun`; a challenge query is answered `w`
(`recRun_recorded`), which is `padFin w` at length `Lc(n)`; the state is kept in both cases. -/
theorem simulate_recHandler_recorded
    (hw : (ans (seedIn n z (List.ofFn ω))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (recDin Lc) (recDout Lc) n) α)
    (s : Fin ((recHandler Lc ans hans).stateLen.eval n) → Bool)
    (hs : (List.ofFn s).headD false = true) :
    simulate ((recHandler Lc ans hans).impl n z ω) c s =
      .pure ((chRun (fun _ => ans (seedIn n z (List.ofFn ω))) c
        (some (padFin _ (ans (seedIn n z (List.ofFn ω)))))).1, s) := by
  induction c with
  | pure a => rw [simulate_pure, chRun_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      have hans0 : (recHandler Lc ans hans).answer n z ω s 0 x = (zeroBits _, s) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, ofFn_zeroBits]
        simp only [recDout_zero, PolyExpr.eval_const]
        exact recRun_dec ans _ _ _
      rw [simulate_query, PolyHandler.impl_apply, hans0, OracleComp.pure_bind, chRun_query_zero]
      exact ih _
    | 1, x, k, ih =>
      have hans1 : (recHandler Lc ans hans).answer n z ω s 1 x =
          (padFin _ (ans (seedIn n z (List.ofFn ω))), s) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
          rw [hw, recDout_one]), seedIn_eq]
        exact recRun_recorded ans _ _ _ hs
      rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
        chRun_query_one_some]
      exact ih _

/-- **The handler's simulation from its initial state** is the deterministic run with the
constant challenge answer `w = ans ⟨1^n, ⟨z, ω⟩⟩` from the unchallenged state, and its final
state is `000` if no challenge was asked and `1 :: mm` for the first challenge query `mm`
(`firstQ`). Requires `|w| = Lc(n)`.

**Proof sketch.** Induction on the computation. Decryption queries are answered `00` and keep
the initial state `000`. The first challenge query `x` is answered `w`, which is `padFin w`, and
records the state `1 :: x`; from there `simulate_recHandler_recorded` applies. -/
theorem simulate_recHandler_init
    (hw : (ans (seedIn n z (List.ofFn ω))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (recDin Lc) (recDout Lc) n) α) :
    ∃ s : Fin ((recHandler Lc ans hans).stateLen.eval n) → Bool,
      simulate ((recHandler Lc ans hans).impl n z ω) c ((recHandler Lc ans hans).init n) =
          .pure ((chRun (fun _ => ans (seedIn n z (List.ofFn ω))) c none).1, s) ∧
        List.ofFn s = (firstQ c).elim [false, false, false] (true :: ·) := by
  have hinit : List.ofFn ((recHandler Lc ans hans).init n) = [false, false, false] := by
    rw [show (recHandler Lc ans hans).init n = zeroBits _ from
        funext (recHandler_init Lc ans hans n),
      ofFn_zeroBits, recHandler_stateLen, PolyExpr.eval_const]
    rfl
  induction c with
  | pure a => exact ⟨_, by rw [simulate_pure, chRun_pure], by rw [firstQ_pure]; exact hinit⟩
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      have hans0 : (recHandler Lc ans hans).answer n z ω ((recHandler Lc ans hans).init n) 0 x =
          (zeroBits _, (recHandler Lc ans hans).init n) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, ofFn_zeroBits]
        simp only [recDout_zero, PolyExpr.eval_const]
        exact recRun_dec ans _ _ _
      obtain ⟨s, hsim, hs⟩ := ih (zeroBits _)
      refine ⟨s, ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, hans0, OracleComp.pure_bind, chRun_query_zero]
        exact hsim
      · rw [firstQ_query_zero]
        exact hs
    | 1, x, k, _ =>
      have hlen : (true :: List.ofFn x).length = (recHandler Lc ans hans).stateLen.eval n := by
        rw [List.length_cons, List.length_ofFn, recHandler_stateLen]
        simp only [recDin_one, PolyExpr.eval_const]
      have hans1 : (recHandler Lc ans hans).answer n z ω ((recHandler Lc ans hans).init n) 1 x =
          (padFin _ (ans (seedIn n z (List.ofFn ω))), padFin _ (true :: List.ofFn x)) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
          rw [hw, recDout_one]), GGMRed.ofFn_padFin_of_length hlen, seedIn_eq]
        refine recRun_fresh ans _ _ _ ?_
        rw [hinit]
        rfl
      refine ⟨padFin _ (true :: List.ofFn x), ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
          chRun_query_one_none]
        exact simulate_recHandler_recorded Lc hans n z ω hw _ _
          (by rw [GGMRed.ofFn_padFin_of_length hlen]; rfl)
      · rw [GGMRed.ofFn_padFin_of_length hlen, firstQ_query_one]
        rfl

end Simulation

end TCSlib.Cryptography.Composability.ChallengeSim
