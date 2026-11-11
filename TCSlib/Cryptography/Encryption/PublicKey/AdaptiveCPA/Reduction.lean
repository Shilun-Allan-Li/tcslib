/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction's game is a hybrid

Let `B` be the machine that T2 (`Games.exists_interactiveHandlerMachine`) builds from the
adversary `A` and the handler `acHandler S cap ist`. This file proves that `B`'s single-challenge
CPA game with bit `b` has the acceptance probability of the hybrid `H_{i⋆(n)+b}`
(`accept_indGame_acHyb`): the first `i⋆` fresh challenges encrypt the right message (the
handler's own encryptions), the `i⋆`-th encrypts `m_b` (the forwarded outer challenge), and the
later ones encrypt the left message.

The proof composes the handler with the outer oracles (`QueryImpl.comp`) and relates the composite,
state by state, to the hybrid with coins given in advance (`tapeImpl`): the handler's state and
the outer challenge state are functions of the hybrid's history (`acAbs`; the outer state is the
`i⋆`-th issued ciphertext once it exists). The handler's tapes, drawn uniformly, then give the lazy
hybrid (`expect_tapeImpl`). Both ends of the run are transported between the game's codec and T2's
(`expect_simulate_castImpl_toCompOn`).

## Main results

* `AdaptiveCPA.castImpl_indImpl_challenge`: the outer challenge oracle on T2's codec.
* `AdaptiveCPA.accept_indGame_acHyb`: `B`'s game with bit `b` is the hybrid `H_{i⋆+b}`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 and the single-to-many hybrid argument (book p. 103).
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

variable (S : FixedLengthPKScheme)

/-- **The outer challenge oracle on T2's codec:** the first challenge `x` samples coins `r`,
answers `c = acEnc S n pk b x r` (read at T2's width) and records it. -/
theorem castImpl_indImpl_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 1).eval n) → Bool) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
        (S.indImpl .cpa b n pk sk) 1 x none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        .pure (padFin ((acDout S 1).eval n) (List.ofFn (acEnc S n pk b x r)),
          some (acEnc S n pk b x r)) := by
  rw [castImpl_eq, S.indImpl_challenge_none_onSpec, OracleComp.bind_assoc]
  congr 1
  funext r
  dsimp only
  rw [OracleComp.pure_bind, ofFn_cast (S.outLens_one n), acEnc_eq, ofFn_select]

/-- The `i`-th issued ciphertext after one more: `(c :: h).reverse[i]?` is `c` at `i = |h|` and
`h.reverse[i]?` otherwise. -/
private theorem getElem?_reverse_cons {α : Type} (c : α) (h : List α) (i : ℕ) :
    (c :: h).reverse[i]? = if i = h.length then some c else h.reverse[i]? := by
  rw [List.reverse_cons]
  by_cases hi : i < h.length
  · rw [List.getElem?_append_left (by rw [List.length_reverse]; exact hi), if_neg (by omega)]
  · rw [List.getElem?_append_right (by rw [List.length_reverse]; omega), List.length_reverse]
    by_cases he : i = h.length
    · rw [if_pos he, he, Nat.sub_self]
      rfl
    · rw [if_neg he, List.getElem?_eq_none (by rw [List.length_singleton]; omega),
        List.getElem?_eq_none (by rw [List.length_reverse]; omega)]

variable (cap : PolyExpr) (ist : ℕ → ℕ)

/-- **The state abstraction:** after the history `h` of issued ciphertexts, the handler's state
records `min |h| κ` fresh challenges and the latest ciphertext `h.headD 0`, and the outer
challenge state is the `i⋆`-th issued ciphertext, if any. -/
private def acAbs (n : ℕ) (h : List (Fin (S.ctLen.eval n) → Bool)) :
    (Fin ((acHandler S cap ist).stateLen.eval n) → Bool) × Option (Fin (S.ctLen.eval n) → Bool) :=
  (acHState S cap ist n (min h.length (cap.eval n)) (h.headD (zeroBits _)), h.reverse[ist n]?)

/-- The selector of `H_{i⋆+b}` at the advised index is `b`. -/
private theorem sel_ist (b : Bool) (m : ℕ) : decide (m < m + b.toNat) = b := by
  cases b
  · rw [Bool.toNat_false, Nat.add_zero, decide_eq_false (Nat.lt_irrefl m)]
  · rw [Bool.toNat_true, decide_eq_true (Nat.lt_succ_self m)]

/-- Away from the advised index the selector of `H_{i⋆+b}` is `[j < i⋆]`. -/
private theorem sel_ne (b : Bool) {j m : ℕ} (h : j ≠ m) :
    decide (j < m + b.toNat) = decide (j < m) := by
  cases b
  · rw [Bool.toNat_false, Nat.add_zero]
  · rw [Bool.toNat_true]
    exact decide_eq_decide.2 ⟨fun h' => by omega, fun h' => by omega⟩

/-- **One call of the composite is one call of the hybrid with coins in advance**, abstracted:
the handler composed with the outer oracles of bit `b`, from `acAbs h`, is the hybrid
`H_{i⋆+b}` with the handler's tapes and the lazy slot `i⋆`, from `h`, with its new history
abstracted.

**Proof sketch.** Decryption: both refuse and keep the state. At the cap: both repeat the
latest ciphertext. Below the cap, away from `i⋆`: the handler encrypts with its tape, which is
the hybrid's coin in advance, and the outer state is unchanged. At `i⋆`: the handler forwards the
challenge, the outer oracle samples coins and encrypts `m_b`, which is the hybrid's lazy slot, and
the outer state becomes the new ciphertext. -/
private theorem comp_acAbs (b : Bool) (n : ℕ) (hist : ist n ≤ cap.eval n) (pk sk : List Bool)
    (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool) (i : Fin 2)
    (x : (bitSpecAt (acDin S) (acDout S) n).dom i) (h : List (Fin (S.ctLen.eval n) → Bool)) :
    (castImpl (S.indImpl .cpa b n pk sk)).comp ((acHandler S cap ist).impl n pk ω) i x
        (acAbs S cap ist n h) =
      (tapeImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
          (cap.eval n) (acEnc S n pk) (fun j => decide (j < ist n + b.toNat))
          (extTape (acSeedTapes S cap ist n ω)) (ist n) i x h).bind
        fun p => .pure (p.1, acAbs S cap ist n p.2) := by
  match i, x with
  | 0, x =>
    rw [QueryImpl.comp_apply, tapeImpl_zero, OracleComp.pure_bind, acAbs]
    dsimp only
    rw [acHandler_impl_dec, simulate_pure, OracleComp.pure_bind]
  | 1, x =>
    rw [QueryImpl.comp_apply]
    by_cases hh : h.length < cap.eval n
    · have hmin : min h.length (cap.eval n) = h.length := Nat.min_eq_left hh.le
      by_cases hk : h.length = ist n
      · -- the advised challenge: forwarded to the outer oracle, the hybrid's lazy slot
        have h2 : h.reverse[ist n]? = none :=
          List.getElem?_eq_none (by rw [List.length_reverse]; omega)
        have hsel : decide (h.length < ist n + b.toNat) = b := by
          rw [hk]
          exact sel_ist b (ist n)
        rw [tapeImpl_lazy (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) _ _ _ _ _ x h hh hk,
          hsel, acAbs]
        dsimp only
        rw [hmin, h2, acHandler_impl_forward S cap ist n pk ω x h.length _ hh hk, simulate_query,
          castImpl_indImpl_challenge, OracleComp.bind_assoc, OracleComp.bind_assoc,
          OracleComp.bind_assoc]
        congr 1
        funext r
        simp only [OracleComp.pure_bind, simulate_pure]
        have he : padFin (S.ctLen.eval n) (List.ofFn (padFin ((acDout S 1).eval n)
            (List.ofFn (acEnc S n pk b x r)))) = acEnc S n pk b x r := by
          rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acDout_one]), padFin_ofFn]
        rw [he, acAbs, List.length_cons, Nat.min_eq_left (by omega), List.headD_cons,
          getElem?_reverse_cons, if_pos hk.symm]
      · -- another fresh challenge: the handler's own encryption with its tape
        rw [tapeImpl_eager (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) _ _ _ _ _ x h hh hk,
          OracleComp.pure_bind, acAbs]
        dsimp only
        rw [hmin, acHandler_impl_eager S cap ist n pk ω x h.length _ hh hk hist, simulate_pure,
          OracleComp.pure_bind, sel_ne b hk, extTape_of_lt _ hh, acAbs, List.length_cons,
          Nat.min_eq_left (by omega), List.headD_cons, getElem?_reverse_cons,
          if_neg (fun e => hk e.symm), acEnc_eq]
    · -- at the cap: the latest ciphertext is repeated
      have hmin : min h.length (cap.eval n) = cap.eval n := Nat.min_eq_right (Nat.le_of_not_lt hh)
      rw [tapeImpl_full (ins := fun i => (acDin S i).eval n)
        (outs := fun i => (acDout S i).eval n) _ _ _ _ _ x h
        (Nat.le_of_not_lt hh), OracleComp.pure_bind, acAbs]
      dsimp only
      rw [hmin, acHandler_impl_full S cap ist n pk ω x _ hist, simulate_pure, OracleComp.pure_bind]

/-- The handler starts from the abstraction of the empty history. -/
private theorem init_acAbs (n : ℕ) :
    ((acHandler S cap ist).init n, (none : Option (Fin (S.ctLen.eval n) → Bool))) =
      acAbs S cap ist n [] := by
  rw [acAbs, acHandler_init_eq, List.length_nil, Nat.zero_min, List.headD_nil, List.reverse_nil,
    List.getElem?_nil]

section Game

variable (A : NUPPT) (q : PolyExpr) (n : ℕ) (B : NUPPT)
  (φ : (Fin ((acHandler S cap ist).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)

/-- **One run of `B`'s game is a run of the hybrid with coins in advance:** with the keys, the
adversary's coins `r` and the handler's seed `ω` fixed, the probability that `B`'s CPA run against
the oracles of bit `b` outputs `1` is the expectation of `A`'s bit against `H_{i⋆+b}` with the
handler's tapes in advance and the lazy slot `i⋆`.

**Proof sketch.** Transport `B`'s run to T2's codec (`indCodec_eq_bitCodec`,
`expect_simulate_castImpl_toCompOn`), replace it by the reduction (T2's equation `hφ`, with
`acHandler_advInput` and `acHandler_finish`), compose the two simulations (`simulate_bind`,
`simulate_comp`) and pass to the hybrid through the state abstraction (`init_acAbs`,
`simulate_eq_of_abs`, `comp_acAbs`). -/
private theorem prob_red_tape (hist : ist n ≤ cap.eval n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((acHandler S cap ist).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((acHandler S cap ist).advInput n z ω) r)
          ((acHandler S cap ist).init n)).bind
          (fun res => (acHandler S cap ist).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((acHandler S cap ist).outLen.eval n)) n
          (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
          z (φ (ω, r)))
    (b : Bool) (pk sk : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
    (r : A.Coins n) :
    ProbComp.prob ((simulate (S.indImpl .cpa b n pk sk) (B.toCompOn (S.indCodec n) n
        (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
        pk (φ (ω, r))) none).bind fun res => .pure (res.1 0)) (· = true) =
      expect (simulate (tapeImpl (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) (cap.eval n) (acEnc S n pk)
          (fun j => decide (j < ist n + b.toNat)) (extTape (acSeedTapes S cap ist n ω)) (ist n))
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) pk r) [])
        (fun p => if (List.ofFn p.1).headD false = true then 1 else 0) := by
  have hd : (acHandler S cap ist).outLen.eval n = 1 := by
    rw [acHandler_outLen, PolyExpr.eval_const]
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
    funext res
    rw [prob_pure, headD_ofFn_one]
  rw [prob_bind, indCodec_eq_bitCodec, h1]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd
    (S.indImpl .cpa b n pk sk) B n _ pk (φ (ω, r)) none
    (fun p => if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
  rw [← hφ pk ω r, acHandler_advInput]
  simp only [acHandler_finish]
  rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
  simp only [OracleComp.pure_bind, simulate_pure, expect_pure]
  rw [init_acAbs,
    simulate_eq_of_abs _ _ (acAbs S cap ist n) (comp_acAbs S cap ist b n hist pk sk ω),
    expect_bind]
  simp only [expect_pure]

/-- **`B`'s game is the hybrid `H_{i⋆+b}`:** if `B` is the machine of T2 for the handler
`acHandler S cap ist` (with the coin bijection `φ` at `n`) and `i⋆(n) ≤ cap(n)`, then `B`'s
single-challenge CPA game with bit `b` and `A`'s hybrid game with the selector `j ↦ [j < i⋆ + b]`
accept with the same probability.

**Proof sketch.** Fix the key-generation coins. `B`'s coins are the handler's seed `ω` and `A`'s
coins `r` (`expect_sample_equiv φ`, `expect_sample_prod`). For fixed `ω` and `r` the run is the
hybrid with the handler's tapes in advance (`prob_red_tape`). The tapes are uniform
(`expect_sample_equiv (acSeedTapes …)`), so averaging over them gives the lazy hybrid
(`expect_tapeImpl`). -/
theorem accept_indGame_acHyb (hist : ist n ≤ cap.eval n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((acHandler S cap ist).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((acHandler S cap ist).advInput n z ω) r)
          ((acHandler S cap ist).init n)).bind
          (fun res => (acHandler S cap ist).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((acHandler S cap ist).outLen.eval n)) n
          (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
          z (φ (ω, r)))
    (b : Bool) :
    accept (S.indGame .cpa B
        (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
        b n) =
      accept (acHyb S A (q.eval n) (cap.eval n) n (fun j => decide (j < ist n + b.toNat))) := by
  rw [accept_eq, accept_eq, S.indGame_eq, acHyb_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  simp only [prob_red_tape S cap ist A q n B φ hist hφ b]
  refine (expect_sample_equiv (acSeedTapes S cap ist n) (fun T => expect (simulate
    (tapeImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (cap.eval n) (acEnc S n (pairFstD (S.gen.runAt n [] rg)))
      (fun j => decide (j < ist n + b.toNat)) (extTape T) (ist n))
    (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
      ((PolyExpr.const 1).eval n)) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r) [])
    (fun p => if (List.ofFn p.1).headD false = true then 1 else 0))).trans ?_
  rw [expect_tapeImpl, prob_bind]
  simp only [prob_pure]

end Game

end TCSlib.Cryptography.Composability.AdaptiveCPA
