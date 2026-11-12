/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The challenge handler

Both machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] run the SIM adversary `A` against
the real experiment's oracles under CPA, answered in the same way:
* `Dec` answers `⊥` (all `false`), as under CPA (`snmImpl_dec_cpa`), without an outer query;
* the first challenge on the parameter `a` asks one outer query, computed from `a`, and answers
  `⟨Y, H⟩` (a ciphertext and a history) computed from `a` and the outer answer; it records
  `⟨Y, H, a⟩`;
* a repeated challenge answers the recorded `⟨Y, H⟩`, without an outer query.

The simulator asks the history oracle and computes `Y` itself; the NM adversary asks its challenge
oracle and computes `H` itself. This file builds the handler once (`chalHandler`), with the outer
query and the two answer parts as parameters (`ChalParams`), and proves its calls on the encoded
states (`chalState`) and that a whole run asks at most one outer query
(`chalHandler_costBoundedBy`).

## Main definitions

* `NMSim.ChalParams`: the parameters of the handler.
* `NMSim.chalHandler`, `NMSim.chalState`.

## Main results

* `NMSim.chalHandler_impl_dec`, `NMSim.chalHandler_impl_some`, `NMSim.chalHandler_impl_none`.
* `NMSim.chalHandler_costBoundedBy`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-- **The parameters of the challenge handler** for inner oracles of parameter length `pl` and
history length `hl`, and `k'` outer oracles with lengths `din'`, `dout'`: the outer oracle `j` of
the challenge, the seed length, the adversary's input, the outer query `qry`, the two answer parts
`ansY` (`ctLen(n)` bits) and `ansH` (`hl(n)` bits), all read from the round input (the last two
with the outer answer in its log), and the finalization. -/
structure ChalParams (pl hl : PolyExpr) (k' : ℕ) (din' dout' : Fin k' → PolyExpr) where
  /-- The outer oracle asked on the first challenge. -/
  j : Fin k'
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The adversary's input, from the context. -/
  advIn : List Bool → List Bool
  /-- It is polynomial-time. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The outer query, from the round input. -/
  qry : List Bool → List Bool
  /-- It is polynomial-time. -/
  qry_poly : PolyTimeComputable qry
  /-- It has the outer query length. -/
  qry_len : ∀ w, (qry w).length = (din' j).eval (rdU w).length
  /-- The ciphertext part of the answer, from the round input with the outer answer. -/
  ansY : List Bool → List Bool
  /-- It is polynomial-time. -/
  ansY_poly : PolyTimeComputable ansY
  /-- It has `ctLen(n)` bits. -/
  ansY_len : ∀ w, (ansY w).length = S.ctLen.eval (rdU w).length
  /-- The history part of the answer, from the round input with the outer answer. -/
  ansH : List Bool → List Bool
  /-- It is polynomial-time. -/
  ansH_poly : PolyTimeComputable ansH
  /-- It has `hl(n)` bits. -/
  ansH_len : ∀ w, (ansH w).length = hl.eval (rdU w).length
  /-- The length of the output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- The finalization's round. -/
  finRun : List Bool → List Bool
  /-- It is polynomial-time. -/
  finRun_poly : PolyTimeComputable finRun

variable {S} {pl hl : PolyExpr} {k' : ℕ} {din' dout' : Fin k' → PolyExpr}

/-- **One round of the challenge handler** on `w = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, with the
state `s = [flag] ‖ Y ‖ H ‖ a`: `Dec` (`i = 0`) returns `⊥ = 0^{msgLen + 1}` and keeps `s`; a
challenge with the flag set returns the recorded `⟨Y, H⟩`; otherwise, with an empty outer log, it
asks `qry w` to the outer oracle `j`, and with the answer in the log it returns `⟨Y, H⟩` and the
state `[true] ‖ Y ‖ H ‖ x`. -/
def chalRun (P : ChalParams S pl hl k' din' dout') (w : List Bool) : List Bool :=
  if decide (rdIdx w = []) then
    pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rdU w).length) false ++
      rdState w)
  else if (rdState w).headD false then
    pairEncode [true] (((rdState w).drop 1).take ((S.ctLen.add hl).eval (rdU w).length) ++
      rdState w)
  else if decide (rdLog w = []) then
    pairEncode [false] (pairEncode (List.replicate P.j true) (P.qry w))
  else
    pairEncode [true] (P.ansY w ++ P.ansH w ++
      (true :: (P.ansY w ++ P.ansH w ++ EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w))))

/-- `chalRun P w` is the round described above. -/
theorem chalRun_eq (P : ChalParams S pl hl k' din' dout') (w : List Bool) :
    chalRun P w =
      if decide (rdIdx w = []) then
        pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rdU w).length) false ++
          rdState w)
      else if (rdState w).headD false then
        pairEncode [true] (((rdState w).drop 1).take ((S.ctLen.add hl).eval (rdU w).length) ++
          rdState w)
      else if decide (rdLog w = []) then
        pairEncode [false] (pairEncode (List.replicate P.j true) (P.qry w))
      else
        pairEncode [true] (P.ansY w ++ P.ansH w ++ (true :: (P.ansY w ++ P.ansH w ++
          EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w)))) := rfl

/-- The round is polynomial-time. -/
theorem polyTimeComputable_chalRun (P : ChalParams S pl hl k' din' dout') :
    PolyTimeComputable (chalRun P) := by
  obtain ⟨hU, -, -, hS, hI, hQ, hL, -⟩ := polyTimeComputable_rd
  have hT := polyTimeComputable_const [true]
  have hY := P.ansY_poly
  have hH := P.ansH_poly
  have hYH : PolyTimeComputable fun w => P.ansY w ++ P.ansH w := hY.append hH
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp hI)
    (hT.pairEncode ((EnsembleLemmas.polyTimeComputable_zeros _ hU).append hS))
    (polyTimeComputable_ite (polyTimeComputable_headD.comp hS)
      (hT.pairEncode (((polyTimeComputable_pairTakePoly (S.ctLen.add hl)).comp
        (hU.pairEncode (polyTimeComputable_tail.comp hS))).congr (fun w => by
          simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]) |>.append hS))
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp hL)
        ((polyTimeComputable_const [false]).pairEncode
          ((polyTimeComputable_const _).pairEncode P.qry_poly))
        (hT.pairEncode (hYH.append (BinArith.polyTimeComputable_cons
          (polyTimeComputable_const [true])
          (hYH.append (EnsembleLemmas.polyTimeComputable_padL pl hU hQ)))))))

/-- **The challenge handler** for the parameters `P`: the state `[flag] ‖ Y ‖ H ‖ a`
(`1 + (ctLen + hl) + pl` bits, initially all `false`), one outer call per inner query, the round
`chalRun P`, and `P`'s seed, adversary input and finalization. -/
def chalHandler (P : ChalParams S pl hl k' din' dout') :
    InteractiveHandler 2 (snmDin S pl) (snmDout S hl) k' din' dout' where
  stateLen := ((PolyExpr.const 1).add (S.ctLen.add hl)).add pl
  seedLen := P.seedLen
  perCall := .const 1
  init _ := zeroBits _
  run := chalRun P
  poly := polyTimeComputable_chalRun P
  advIn := P.advIn
  advIn_poly := P.advIn_poly
  outLen := P.outLen
  finCall := P.finCall
  finRun := P.finRun
  finRun_poly := P.finRun_poly

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall advIn outLen finCall
  finRun] chalHandler

section State

variable (P : ChalParams S pl hl k' din' dout') (n : ℕ)

/-- The state has `1 + (ctLen(n) + hl(n)) + pl(n)` bits. -/
theorem chalHandler_stateLen_eval :
    (chalHandler P).stateLen.eval n = 1 + (S.ctLen.eval n + hl.eval n) + pl.eval n := by
  rw [chalHandler_stateLen, PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_add,
    PolyExpr.eval_const]

/-- **The encoded states:** `none` (no challenge yet) is all `false`, and `some (Y, H, a)` is
`[true] ‖ Y ‖ H ‖ a`. -/
def chalState
    (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    Fin ((chalHandler P).stateLen.eval n) → Bool :=
  match o with
  | none => zeroBits _
  | some (y, h, a) => padFin _ (true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a))

/-- `chalState P n none = 0`. -/
theorem chalState_none : chalState P n none = zeroBits _ := rfl

/-- `chalState P n (some (Y, H, a)) = padFin _ ([true] ‖ Y ‖ H ‖ a)`. -/
theorem chalState_some (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    chalState P n (some (y, h, a)) =
      padFin _ (true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a)) := rfl

/-- The initial state is `chalState P n none`. -/
theorem chalHandler_init : (chalHandler P).init n = chalState P n none := rfl

/-- The encoded state `some (Y, H, a)` as a string: `[true] ‖ Y ‖ H ‖ a`. -/
theorem ofFn_chalState_some (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    List.ofFn (chalState P n (some (y, h, a))) =
      true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a) := by
  rw [chalState_some]
  refine GGMRed.ofFn_padFin_of_length ?_
  rw [List.length_cons, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_ofFn, chalHandler_stateLen_eval]
  omega

/-- The encoded state `none` as a string is all `false`. -/
theorem ofFn_chalState_none :
    List.ofFn (chalState P n none) =
      List.replicate ((chalHandler P).stateLen.eval n) false := by
  rw [chalState_none, ofFn_zeroBits]

/-- The first bit of an encoded state tells whether a challenge was recorded. -/
theorem headD_ofFn_chalState
    (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    (List.ofFn (chalState P n o)).headD false = o.isSome := by
  cases o with
  | none =>
    rw [ofFn_chalState_none, chalHandler_stateLen_eval, Nat.add_assoc, Nat.add_comm,
      List.replicate_succ, List.headD_cons]
    rfl
  | some yha =>
    obtain ⟨y, h, a⟩ := yha
    rw [ofFn_chalState_some, List.headD_cons]
    rfl

end State

/-- A padded run of `false`s is all `false`: `padFin d (0^m) = 0`. -/
private theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
  funext i
  rw [padFin_apply, zeroBits_apply]
  by_cases h : (i : ℕ) < m
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]

section Calls

variable (P : ChalParams S pl hl k' din' dout') (n : ℕ) (z : List Bool)
  (ω : Fin ((chalHandler P).seedLen.eval n) → Bool)

/-- **`Dec` answers `⊥` and keeps the state**, asking nothing. -/
theorem chalHandler_impl_dec (x : Fin ((snmDin S pl 0).eval n) → Bool)
    (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) ×
      (Fin (pl.eval n) → Bool))) :
    (chalHandler P).impl n z ω 0 x (chalState P n o) = .pure (zeroBits _, chalState P n o) := by
  obtain ⟨hU, -, -, hS, hI, -, -⟩ := fields_input (k := 2) n z (List.ofFn ω)
    (List.ofFn (chalState P n o)) 0 (List.ofFn x) []
  rw [impl_of_ret (chalHandler P) n z ω 0 x (chalState P n o)
    (List.replicate ((S.msgLen.add (.const 1)).eval n) false) (List.ofFn (chalState P n o))
    (by rw [List.length_replicate, snmDout_zero]) List.length_ofFn (by
      show chalRun P _ = _
      rw [chalRun_eq, hI, hU, hS, List.length_replicate]
      rfl), padFin_replicate_false, padFin_ofFn]

/-- **A repeated challenge answers the recorded `⟨Y, H⟩`** and keeps the state, asking nothing. -/
theorem chalHandler_impl_some (x : Fin ((snmDin S pl 1).eval n) → Bool)
    (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool) (a : Fin (pl.eval n) → Bool) :
    (chalHandler P).impl n z ω 1 x (chalState P n (some (y, h, a))) =
      .pure (padFin _ (List.ofFn y ++ List.ofFn h), chalState P n (some (y, h, a))) := by
  obtain ⟨hU, -, -, hS, hI, -, -⟩ := fields_input (k := 2) n z (List.ofFn ω)
    (List.ofFn (chalState P n (some (y, h, a)))) 1 (List.ofFn x) []
  have hans : ((List.ofFn (chalState P n (some (y, h, a)))).drop 1).take
      ((S.ctLen.add hl).eval n) = List.ofFn y ++ List.ofFn h := by
    rw [ofFn_chalState_some, List.drop_one, List.tail_cons, PolyExpr.eval_add]
    exact List.take_left' (by rw [List.length_append, List.length_ofFn, List.length_ofFn])
  rw [impl_of_ret (chalHandler P) n z ω 1 x _ (List.ofFn y ++ List.ofFn h)
    (List.ofFn (chalState P n (some (y, h, a))))
    (by rw [List.length_append, List.length_ofFn, List.length_ofFn, snmDout_one, PolyExpr.eval_add])
    List.length_ofFn (by
      show chalRun P _ = _
      rw [chalRun_eq, hI, hU, hS, List.length_replicate, headD_ofFn_chalState, hans]
      rfl), padFin_ofFn]

/-- **A first challenge asks one outer query:** on the parameter `x` in the empty state it asks
`qry w₀` to the outer oracle `j` (`w₀` the round input with the empty log) and, on the answer `y`,
answers `⟨Y, H⟩ = ⟨ansY w₁, ansH w₁⟩` (`w₁` the round input with `y` in the log), recording
`⟨Y, H, x⟩`. -/
theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
    (chalHandler P).impl n z ω 1 x (chalState P n none) =
      .query P.j (padFin _ (P.qry (InteractiveHandler.input n z (List.ofFn ω)
          (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) [])))
        fun y : Fin ((dout' P.j).eval n) → Bool =>
          .pure (padFin _ (P.ansY (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) [])) (List.ofFn y))) [])) ++
            P.ansH (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) [])) (List.ofFn y))) []))),
          chalState P n (some (padFin _ (P.ansY (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) [])) (List.ofFn y))) []))),
            padFin _ (P.ansH (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) [])) (List.ofFn y))) []))),
            padFin (pl.eval n) (List.ofFn x)))) := by
  set w₀ := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (chalState P n none)) (1 : Fin 2)
    (List.ofFn x) [] with hw₀
  obtain ⟨hU₀, -, -, hS₀, hI₀, -, hL₀⟩ := fields_input (k := 2) n z (List.ofFn ω)
    (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
  have hq : List.ofFn (padFin ((din' P.j).eval n) (P.qry w₀)) = P.qry w₀ :=
    GGMRed.ofFn_padFin_of_length (by rw [P.qry_len, hU₀, List.length_replicate])
  have hxl : (List.ofFn x).length = pl.eval n := by
    rw [List.length_ofFn]
    show (snmDin S pl 1).eval n = _
    rw [snmDin_one]
  have hx : EnsembleLemmas.padL (pl.eval n) (List.ofFn x) =
      List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
    rw [EnsembleLemmas.padL_eq, GGMRed.ofFn_padFin_of_length hxl]
    exact List.take_left' hxl
  have hpc : 1 ≤ (chalHandler P).perCall.eval n := by
    rw [chalHandler_perCall, PolyExpr.eval_const]
  set W₁ : (Fin ((dout' P.j).eval n) → Bool) → List Bool := fun y =>
    InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
    with hW₁
  have hY : ∀ y, (P.ansY (W₁ y)).length = S.ctLen.eval n := fun y => by
    rw [P.ansY_len, hW₁, (fields_input (k := 2) n z _ _ 1 _ _).1, List.length_replicate]
  have hH : ∀ y, (P.ansH (W₁ y)).length = hl.eval n := fun y => by
    rw [P.ansH_len, hW₁, (fields_input (k := 2) n z _ _ 1 _ _).1, List.length_replicate]
  rw [impl_of_query (chalHandler P) n z ω 1 x (chalState P n none) P.j (padFin _ (P.qry w₀))
    (fun y => P.ansY (W₁ y) ++ P.ansH (W₁ y))
    (fun y => List.ofFn (chalState P n (some (padFin _ (P.ansY (W₁ y)), padFin _ (P.ansH (W₁ y)),
      padFin (pl.eval n) (List.ofFn x)))))
    (fun y => by rw [List.length_append, hY, hH, snmDout_one, PolyExpr.eval_add])
    (fun y => List.length_ofFn) hpc ?_ (fun y => ?_)]
  · refine congrArg _ (funext fun y => ?_)
    rw [padFin_ofFn (chalState P n (some (padFin _ (P.ansY (W₁ y)), padFin _ (P.ansH (W₁ y)),
      padFin (pl.eval n) (List.ofFn x))))]
  · show chalRun P _ = _
    rw [chalRun_eq, hI₀, hU₀, hS₀, hL₀, List.length_replicate, headD_ofFn_chalState, hq]
    rfl
  · rw [hq]
    obtain ⟨hU₁, -, -, hS₁, hI₁, hQ₁, hL₁⟩ := fields_input (k := 2) n z (List.ofFn ω)
      (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
    show chalRun P (W₁ y) = _
    beta_reduce
    rw [chalRun_eq, hW₁]
    beta_reduce
    rw [hI₁, hU₁, hS₁, hL₁, hQ₁, List.length_replicate, headD_ofFn_chalState, hx,
      ofFn_chalState_some, GGMRed.ofFn_padFin_of_length (hY y), GGMRed.ofFn_padFin_of_length (hH y)]
    rw [if_neg (by simp), if_neg (by simp),
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]

/-- **A whole run asks at most one outer query:** from the initial state, the simulation of any
computation by the challenge handler is `CostBoundedBy 1` (one per outer query).

**Proof sketch.** `simulate_costBoundedBy_once` with the encoded states as the invariant and the
recorded ones as used: `Dec` and repeated challenges are free (`chalHandler_impl_dec`,
`chalHandler_impl_some`), and the first challenge asks one query and records
(`chalHandler_impl_none`). -/
theorem chalHandler_costBoundedBy {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α) :
    (simulate ((chalHandler P).impl n z ω) c (chalState P n none)).CostBoundedBy
      (fun _ => 1) 1 := by
  classical
  have hne : ∀ y h a, chalState P n none ≠ chalState P n (some (y, h, a)) := by
    intro y h a heq
    have := congrArg (fun s => (List.ofFn s).headD false) heq
    simp only [headD_ofFn_chalState, Option.isSome_none, Option.isSome_some] at this
    exact Bool.false_ne_true this
  have key := simulate_costBoundedBy_once ((chalHandler P).impl n z ω) (fun _ => 1)
    (fun s => ∃ o, s = chalState P n o) (fun s => ∃ y h a, s = chalState P n (some (y, h, a)))
    (fun i x s _ hu => ?_) (fun i x s hg hu => ?_) c (chalState P n none) ⟨none, rfl⟩
  · rwa [if_neg (fun ⟨y, h, a, heq⟩ => hne y h a heq)] at key
  · obtain ⟨y, h, a, rfl⟩ := hu
    match i, x with
    | 0, x =>
      rw [chalHandler_impl_dec]
      exact ⟨OracleComp.costBoundedBy_pure _ _ _, ⟨some (y, h, a), rfl⟩, ⟨y, h, a, rfl⟩⟩
    | 1, x =>
      rw [chalHandler_impl_some]
      exact ⟨OracleComp.costBoundedBy_pure _ _ _, ⟨some (y, h, a), rfl⟩, ⟨y, h, a, rfl⟩⟩
  · obtain ⟨o, rfl⟩ := hg
    cases o with
    | some yha => exact absurd ⟨yha.1, yha.2.1, yha.2.2, rfl⟩ hu
    | none =>
      match i, x with
      | 0, x =>
        rw [chalHandler_impl_dec]
        exact Or.inl ⟨OracleComp.costBoundedBy_pure _ _ _, ⟨none, rfl⟩, hu⟩
      | 1, x =>
        rw [chalHandler_impl_none]
        exact Or.inr ⟨(OracleComp.costBoundedBy_query _ _ _ _ _).2 ⟨le_rfl, fun _ =>
          OracleComp.costBoundedBy_pure _ _ _⟩, fun _ => ⟨⟨some (_, _, padFin _ (List.ofFn x)), rfl⟩, ⟨_, _, padFin _ (List.ofFn x), rfl⟩⟩⟩

end Calls

end TCSlib.Cryptography.Composability.NMSim
