/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A query-recording handler with advice

A reduction from CPA security whose challenge answer depends on the challenge query
[PS10, the hybrid argument of p. 103 in the game of Definition 171.5] runs the adversary once. It
answers every decryption query with `⊥` and the first challenge query `x` with a string computed
from its context, a fixed advice string `aux` and `x`; it records `x` and answers every later
challenge query as it answered the first. This file builds that handler as a `Games.PolyHandler`
(`qHandler`), generic in the lengths, the advice, the answer and the finalization, and combines
it with T1 (`Games.exists_handlerMachine`): the resulting machine's output is the finalization of
the deterministic run `ChallengeSim.chRun` with the answer function, on the advice and the
first challenge query (`exists_qHandlerMachine`).

## Main definitions

* `BitwiseSim.qDin`, `qDout`: the query and answer lengths of the two oracles.
* `BitwiseSim.qRun`: the handler's step as a string function.
* `BitwiseSim.qHandler`: the handler; its state is `⟨aux, asked :: x⟩`.

## Main results

* `BitwiseSim.simulate_qHandler_recorded`, `simulate_qHandler_init`: the handler's simulation is
  the deterministic run with the answer function, and its final state records the first
  challenge query.
* `BitwiseSim.chRun_toCompOn_transport_list`: transport of a run with a query-dependent answer
  along equal lengths.
* `BitwiseSim.exists_qHandlerMachine`: the machine of the handler, by T1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the hybrid argument) and §7.1.4, Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim

/-! ### Lengths -/

/-- The query lengths: `Lc(n)`-bit ciphertexts to oracle `0` (decryption), `Lq(n)`-bit challenge
queries to oracle `1`. -/
def qDin (Lc Lq : PolyExpr) : Fin 2 → PolyExpr
  | 0 => Lc
  | 1 => Lq

/-- Decryption queries have `Lc(n)` bits: `qDin Lc Lq 0 = Lc`. -/
theorem qDin_zero (Lc Lq : PolyExpr) : qDin Lc Lq 0 = Lc := rfl

/-- Challenge queries have `Lq(n)` bits: `qDin Lc Lq 1 = Lq`. -/
theorem qDin_one (Lc Lq : PolyExpr) : qDin Lc Lq 1 = Lq := rfl

/-- The answer lengths: `Ld(n)`-bit decryption answers and `Lc(n)`-bit challenge ciphertexts. -/
def qDout (Ld Lc : PolyExpr) : Fin 2 → PolyExpr
  | 0 => Ld
  | 1 => Lc

/-- Decryption answers have `Ld(n)` bits: `qDout Ld Lc 0 = Ld`. -/
theorem qDout_zero (Ld Lc : PolyExpr) : qDout Ld Lc 0 = Ld := rfl

/-- Challenge answers have `Lc(n)` bits: `qDout Ld Lc 1 = Lc`. -/
theorem qDout_one (Ld Lc : PolyExpr) : qDout Ld Lc 1 = Lc := rfl

/-! ### The step function -/

/-- **One step of the handler** on `⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩` with state `s = ⟨aux, t⟩`. A challenge
query (`i = 1`) is answered with `ans ⟨ctx, ⟨aux, y⟩⟩`, where `y` is the recorded query
`t.drop 1` if the flag `t.headD false` is set, and `x` otherwise; in the second case the new
state is `⟨aux, 1 :: x⟩`, else the state is kept. A decryption query (`i = 0`) is answered with
the empty string (decoded as all-`false`) and keeps the state. -/
def qRun (ans : List Bool → List Bool) (w : List Bool) : List Bool :=
  if (pairFstD (pairSndD (pairSndD w))).headD false then
    if (pairSndD (pairFstD (pairSndD w))).headD false then
      pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
          ((pairSndD (pairFstD (pairSndD w))).drop 1))))
        (pairFstD (pairSndD w))
    else
      pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
          (pairSndD (pairSndD (pairSndD w))))))
        (pairEncode (pairFstD (pairFstD (pairSndD w))) (true :: pairSndD (pairSndD (pairSndD w))))
  else pairEncode [] (pairFstD (pairSndD w))

/-- The defining equation of `qRun`: on `⟨ctx, ⟨⟨aux, t⟩, ⟨1^i, x⟩⟩⟩`, a challenge query (`i = 1`)
returns `⟨ans ⟨ctx, ⟨aux, t.drop 1⟩⟩, ⟨aux, t⟩⟩` when the flag `t.headD false` is set, and
`⟨ans ⟨ctx, ⟨aux, x⟩⟩, ⟨aux, 1 :: x⟩⟩` otherwise; a decryption query returns `⟨[], ⟨aux, t⟩⟩`. -/
theorem qRun_eq (ans : List Bool → List Bool) (w : List Bool) :
    qRun ans w =
      if (pairFstD (pairSndD (pairSndD w))).headD false then
        if (pairSndD (pairFstD (pairSndD w))).headD false then
          pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
              ((pairSndD (pairFstD (pairSndD w))).drop 1))))
            (pairFstD (pairSndD w))
        else
          pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
              (pairSndD (pairSndD (pairSndD w))))))
            (pairEncode (pairFstD (pairFstD (pairSndD w)))
              (true :: pairSndD (pairSndD (pairSndD w))))
      else pairEncode [] (pairFstD (pairSndD w)) := rfl

/-- A decryption query is answered with the empty string and keeps the state:
`qRun ans ⟨ctx, ⟨s, ⟨[], x⟩⟩⟩ = ⟨[], s⟩`. -/
theorem qRun_dec (ans : List Bool → List Bool) (ctx s x : List Bool) :
    qRun ans (pairEncode ctx (pairEncode s (pairEncode [] x))) = pairEncode [] s := by
  simp only [qRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_nil,
    Bool.false_eq_true, if_false]

/-- The first challenge query `x` (flag unset) is answered with `ans ⟨ctx, ⟨aux, x⟩⟩` and recorded
as the state `⟨aux, 1 :: x⟩`. -/
theorem qRun_fresh (ans : List Bool → List Bool) (ctx aux t x : List Bool)
    (ht : t.headD false = false) :
    qRun ans (pairEncode ctx (pairEncode (pairEncode aux t) (pairEncode [true] x))) =
      pairEncode (ans (pairEncode ctx (pairEncode aux x))) (pairEncode aux (true :: x)) := by
  simp only [qRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true, ht,
    Bool.false_eq_true, if_false]

/-- A later challenge query (state `⟨aux, 1 :: x⟩`) is answered with `ans ⟨ctx, ⟨aux, x⟩⟩` and
keeps the state. -/
theorem qRun_recorded (ans : List Bool → List Bool) (ctx aux x y : List Bool) :
    qRun ans (pairEncode ctx (pairEncode (pairEncode aux (true :: x)) (pairEncode [true] y))) =
      pairEncode (ans (pairEncode ctx (pairEncode aux x))) (pairEncode aux (true :: x)) := by
  simp only [qRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true,
    List.drop_succ_cons, List.drop_zero]

/-- The step function is polynomial-time when `ans` is.

**Proof sketch.** Pair projections, `polyTimeComputable_headD` for the two tests,
`polyTimeComputable_tail` for the recorded query, and `polyTimeComputable_ite` for the cases. -/
theorem polyTimeComputable_qRun {ans : List Bool → List Bool} (hans : PolyTimeComputable ans) :
    PolyTimeComputable (qRun ans) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD w) := hF.comp hS
  have haux : PolyTimeComputable fun w => pairFstD (pairFstD (pairSndD w)) := hF.comp hs
  have ht : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD w)) := hS.comp hs
  have hx : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) := hS.comp (hS.comp hS)
  have hi : PolyTimeComputable fun w => [(pairFstD (pairSndD (pairSndD w))).headD false] :=
    polyTimeComputable_headD.comp (hF.comp (hS.comp hS))
  have hflag : PolyTimeComputable fun w => [(pairSndD (pairFstD (pairSndD w))).headD false] :=
    polyTimeComputable_headD.comp ht
  have hrec := (hans.comp (hF.pairEncode
    (haux.pairEncode (polyTimeComputable_tail.comp ht)))).pairEncode hs
  have hnew := (hans.comp (hF.pairEncode (haux.pairEncode hx))).pairEncode
    (haux.pairEncode ((polyTimeComputable_const [true]).append hx))
  exact polyTimeComputable_ite hi (polyTimeComputable_ite hflag hrec hnew)
    ((polyTimeComputable_const []).pairEncode hs)

/-! ### The handler -/

/-- **The query-recording handler** with ciphertext length `Lc`, challenge-query length `Lq`,
decryption-answer length `Ld`, advice `aux` (of length `Laux(n)`), seed length `Lseed`, answer
`ans` and finalization `fin`: state `⟨aux n, asked :: x⟩`, initially `⟨aux n, 0^{1 + Lq(n)}⟩`;
the adversary runs on `pk`, the first component of the reduction input; the step is `qRun ans`
and the output is `fin`. -/
noncomputable def qHandler (Lc Lq Ld Laux Lseed : PolyExpr) (aux : ℕ → List Bool)
    (ans : List Bool → List Bool) (hans : PolyTimeComputable ans)
    (fin : List Bool → List Bool) (hfin : PolyTimeComputable fin) :
    PolyHandler 2 (qDin Lc Lq) (qDout Ld Lc) where
  stateLen := .add (.add (.mul (.const 2) Laux) (.const 3)) Lq
  seedLen := Lseed
  init n := padFin _ (pairEncode (aux n) (false :: List.replicate (Lq.eval n) false))
  run := qRun ans
  poly := polyTimeComputable_qRun hans
  advIn := recAdvIn
  advIn_poly := by
    have h : PolyTimeComputable fun ctx => pairFstD (pairFstD (pairSndD ctx)) :=
      polyTimeComputable_pairFstD.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
    rw [show recAdvIn = fun ctx => pairFstD (pairFstD (pairSndD ctx)) from funext recAdvIn_eq]
    exact h
  out := fin
  out_poly := hfin

attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out] qHandler

/-! ### The handler's simulation -/

section Simulation

variable {α : Type} (Lc Lq Ld Laux Lseed : PolyExpr) (aux : ℕ → List Bool)
  {ans : List Bool → List Bool} (hans : PolyTimeComputable ans)
  {fin : List Bool → List Bool} (hfin : PolyTimeComputable fin)
  (n : ℕ) (z : List Bool)
  (ω : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).seedLen.eval n) → Bool)

/-- A decryption query is answered all-`false` and keeps the state:
`(qHandler …).answer n z ω s 0 x = (zeroBits _, s)`. -/
theorem qHandler_answer_dec
    (s : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n) → Bool)
    (x : Fin ((qDin Lc Lq 0).eval n) → Bool) :
    (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).answer n z ω s 0 x = (zeroBits _, s) := by
  have h : pairDecode ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).run
      (PolyHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x))) =
      some ([], List.ofFn s) := by
    rw [qHandler_run, PolyHandler.input_eq]
    exact (congrArg pairDecode (qRun_dec ans _ _ _)).trans (pairDecode_pairEncode _ _)
  rw [PolyHandler.answer_of_pairDecode_eq_some _ h, decodeFin_nil_getD, decodeFin_ofFn,
    Option.getD_some]

/-- **After the challenge `mm` is recorded**, the handler's simulation is the deterministic run
with the answer function `g y = ans ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨aux n, y⟩⟩` from the recorded state
`padFin (g mm)`, and the handler's state does not change. Requires `|g y| = Lc(n)`.

**Proof sketch.** Induction on the computation. A decryption query is answered all-`false`
(`qRun_dec`), the answer of `chRun`; a challenge query is answered `g mm` (`qRun_recorded`),
which is `padFin (g mm)` at length `Lc(n)`; the state is kept in both cases. -/
theorem simulate_qHandler_recorded
    (hw : ∀ y : List Bool, y.length = Lq.eval n →
      (ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (qDin Lc Lq) (qDout Ld Lc) n) α)
    (mm : Fin ((qDin Lc Lq 1).eval n) → Bool)
    (s : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n) → Bool)
    (hs : List.ofFn s = pairEncode (aux n) (true :: List.ofFn mm)) :
    simulate ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).impl n z ω) c s =
      .pure ((chRun (fun y => ans (pairEncode (seedIn n z (List.ofFn ω))
        (pairEncode (aux n) (List.ofFn y)))) c
        (some (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
          (pairEncode (aux n) (List.ofFn mm))))))).1, s) := by
  induction c with
  | pure a => rw [simulate_pure, chRun_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, PolyHandler.impl_apply, qHandler_answer_dec, OracleComp.pure_bind,
        chRun_query_zero]
      exact ih _
    | 1, x, k, ih =>
      have hlen : (List.ofFn mm).length = Lq.eval n := by simp only [List.length_ofFn, qDin_one]
      have hans1 : (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).answer n z ω s 1 x =
          (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (aux n) (List.ofFn mm)))), s) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [qHandler_run, PolyHandler.input_eq, ofFn_padFin_of_length (by
          rw [hw _ hlen, qDout_one]), hs, seedIn_eq]
        exact qRun_recorded ans _ _ _ _
      rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
        chRun_query_one_some]
      exact ih _

/-- **The handler's simulation from its initial state** is the deterministic run with the answer
function `g y = ans ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨aux n, y⟩⟩` from the unchallenged state, and its final
state is `⟨aux n, 0^{1 + Lq(n)}⟩` if no challenge was asked and `⟨aux n, 1 :: mm⟩` for the first
challenge query `mm` (`firstQ`). Requires `|aux n| = Laux(n)` and `|g y| = Lc(n)`.

**Proof sketch.** Induction on the computation. Decryption queries are answered all-`false` and
keep the initial state. The first challenge query `x` is answered `g x`, which is
`padFin (g x)`, and records the state `⟨aux n, 1 :: x⟩` (`qRun_fresh`); from there
`simulate_qHandler_recorded` applies. -/
theorem simulate_qHandler_init (haux : (aux n).length = Laux.eval n)
    (hw : ∀ y : List Bool, y.length = Lq.eval n →
      (ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (qDin Lc Lq) (qDout Ld Lc) n) α) :
    ∃ s : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n) → Bool,
      simulate ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).impl n z ω) c
          ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n) =
          .pure ((chRun (fun y => ans (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (aux n) (List.ofFn y)))) c none).1, s) ∧
        List.ofFn s = pairEncode (aux n)
          ((firstQ c).elim (false :: List.replicate (Lq.eval n) false) (true :: ·)) := by
  have hinit : List.ofFn ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n) =
      pairEncode (aux n) (false :: List.replicate (Lq.eval n) false) := by
    rw [show (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n =
        padFin _ (pairEncode (aux n) (false :: List.replicate (Lq.eval n) false)) from
      funext (qHandler_init Lc Lq Ld Laux Lseed aux ans hans fin hfin n)]
    refine ofFn_padFin_of_length ?_
    rw [qHandler_stateLen, length_pairEncode, List.length_cons, List.length_replicate, haux]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  induction c with
  | pure a => exact ⟨_, by rw [simulate_pure, chRun_pure], by rw [firstQ_pure]; exact hinit⟩
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      obtain ⟨s, hsim, hs⟩ := ih (zeroBits _)
      refine ⟨s, ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, qHandler_answer_dec, OracleComp.pure_bind,
          chRun_query_zero]
        exact hsim
      · rw [firstQ_query_zero]
        exact hs
    | 1, x, k, _ =>
      have hxlen : (List.ofFn x).length = Lq.eval n := by simp only [List.length_ofFn, qDin_one]
      have hlen : (pairEncode (aux n) (true :: List.ofFn x)).length =
          (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n := by
        rw [qHandler_stateLen, length_pairEncode, List.length_cons, hxlen, haux]
        simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
        omega
      have hans1 : (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).answer n z ω
          ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n) 1 x =
          (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (aux n) (List.ofFn x)))),
            padFin _ (pairEncode (aux n) (true :: List.ofFn x))) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [qHandler_run, PolyHandler.input_eq, ofFn_padFin_of_length (by
          rw [hw _ hxlen, qDout_one]), ofFn_padFin_of_length hlen, hinit, seedIn_eq]
        exact qRun_fresh ans _ _ _ _ rfl
      refine ⟨padFin _ (pairEncode (aux n) (true :: List.ofFn x)), ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
          chRun_query_one_none]
        exact simulate_qHandler_recorded Lc Lq Ld Laux Lseed aux hans hfin n z ω hw _ x _
          (ofFn_padFin_of_length hlen)
      · rw [ofFn_padFin_of_length hlen, firstQ_query_one]
        rfl

end Simulation

/-! ### Transport and the machine -/

/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
`G : List Bool → List Bool`,
`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
the two runs have the same `firstQ`.

**Proof sketch.** Substitute the equalities; both sides become identical. -/
theorem chRun_toCompOn_transport_list {ins outs ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (G : List Bool → List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
  subst hi ho hd
  exact ⟨rfl, rfl⟩

/-- **The machine of the query-recording handler** (T1 for `qHandler`). For a machine adversary
`A` with query budget `q` and one-bit output, there is a machine `D` and, at every parameter, a
bijection `φ` from (seed, `A`'s coins) to `D`'s coins with the following property. For lengths
`ins`, `outs` equal to those of `qDin Lc Lq`, `qDout Ld Lc`, let `c` be `A`'s computation on
`pairFstD z` with coins `r` through `bitCodec ins outs 1`, `ctx = ⟨1^n, ⟨z, ω⟩⟩` and
`g y = ans ⟨ctx, ⟨aux n, y⟩⟩`. If `|aux n| = Laux(n)` and `|g y| = Lc(n)` for every
`Lq(n)`-bit `y`, then `D` on `z` with coins `φ (ω, r)` outputs
`fin ⟨ctx, ⟨⟨aux n, t⟩, chRun g c⟩⟩`, where `t` is `1 :: mm` for the first challenge query `mm`
of `c` and `0^{1 + Lq(n)}` without one.

**Proof sketch.** T1 (`Games.exists_handlerMachine`) for `qHandler` with `dα = 1`; the handler's
simulation is `simulate_qHandler_init`; its adversary input is `pairFstD z` (`recAdvIn_eq`); the
run and the first challenge query transport to the lengths `ins`, `outs`
(`chRun_toCompOn_transport_list`). -/
theorem exists_qHandlerMachine (A : NUPPT) (q : PolyExpr) (Lc Lq Ld Laux Lseed : PolyExpr)
    (aux : ℕ → List Bool) (haux : ∀ n, (aux n).length = Laux.eval n)
    (ans : List Bool → List Bool) (hans : PolyTimeComputable ans)
    (fin : List Bool → List Bool) (hfin : PolyTimeComputable fin) :
    ∃ D : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (Lseed.eval n) → Bool) × A.Coins n ≃ D.Coins n,
      ∀ (ins outs : Fin 2 → ℕ), (fun i => (qDin Lc Lq i).eval n) = ins →
        (fun i => (qDout Ld Lc i).eval n) = outs →
        ∀ (z : List Bool) (ω : Fin (Lseed.eval n) → Bool) (r : A.Coins n),
          (∀ y : List Bool, y.length = Lq.eval n →
            (ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y))).length =
              Lc.eval n) →
          D.runAt n z (φ (ω, r)) =
            fin (pairEncode (seedIn n z (List.ofFn ω))
              (pairEncode (pairEncode (aux n)
                ((firstQ (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r)).elim
                  (false :: List.replicate (Lq.eval n) false) (true :: ·)))
                (List.ofFn (chRun (fun y => ans (pairEncode (seedIn n z (List.ofFn ω))
                    (pairEncode (aux n) (List.ofFn y))))
                  (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r) none).1))) := by
  obtain ⟨D, hD⟩ := exists_handlerMachine A q (qDin Lc Lq) (qDout Ld Lc) (.const 1)
    (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin)
  refine ⟨D, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hD n
  refine ⟨φ, fun ins outs hi ho z ω r hw => ?_⟩
  obtain ⟨a, s, hsim, hrun⟩ := hφ z ω r
  have hadv : (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).advInput n z ω = pairFstD z := by
    rw [PolyHandler.advInput_eq, qHandler_advIn, recAdvIn_eq, seedIn_eq, pairSndD_pairEncode,
      pairFstD_pairEncode]
  obtain ⟨s', hsim', hs'⟩ := simulate_qHandler_init Lc Lq Ld Laux Lseed aux hans hfin n z ω
    (haux n) hw _
  rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
  obtain ⟨rfl, rfl⟩ := hsim'
  obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport_list hi ho (PolyExpr.eval_const 1 n) A n (q.eval n)
    ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).advInput n z ω) r
    (fun y => ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y)))
  rw [hadv] at h₁ h₂ hs'
  refine hrun.trans ?_
  rw [PolyHandler.result_eq, qHandler_out, hadv, hs', h₂, h₁]

end TCSlib.Cryptography.Composability.BitwiseSim
