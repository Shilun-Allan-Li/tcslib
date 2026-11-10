/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive left-or-right public-key security

An extension of the fixed-length game of [PS10, Definition 171.5] with one hidden bit,
one generated key pair, and a polynomial cap on fresh challenges. The adversary may
choose each pair of messages after seeing the earlier answers. In the CCA2 game the
decryptor refuses every ciphertext already issued as a challenge.

## Main definitions

* `FixedLengthPKScheme.adaptiveIndImpl` implements the two oracles and their history.
* `FixedLengthPKScheme.adaptiveIndGame` runs the existing adversary codec with those oracles.
* `FixedLengthPKScheme.AdaptiveINDSecure` is the negligible-advantage condition.

## Main results

* `FixedLengthPKScheme.adaptiveIndGame_one` recovers the exact single-challenge game.
* `FixedLengthPKScheme.AdaptiveINDSecure.single` specializes the security predicate.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-- Extend [PS10, Definition 171.5] to a bounded list of fresh left-or-right challenges.
The history records each issued challenge. A decryption query in the history receives
the existing refusal reply. Once the challenge cap is reached the game repeats the
latest ciphertext, with a zero reply for a zero cap and empty history. The history is
a list so a repeated ciphertext still consumes one fresh challenge. -/
noncomputable def adaptiveIndImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (cap : ℕ) : QueryImpl (S.indSpec n) (List (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, history =>
    if cast (S.indSpec_decDom n) c ∈ history then
      .pure (zeroBits _, history)
    else
      (S.indImpl atk b n pk sk 0 c history.head?).bind fun res => .pure (res.1, history)
  | 1, mm, history =>
    if history.length < cap then
      (S.indImpl atk b n pk sk 1 mm none).bind fun res => .pure (res.1, res.2.toList ++ history)
    else
      match history.head? with
      | none => .pure (zeroBits _, history)
      | some c =>
        (S.indImpl atk b n pk sk 1 mm (some c)).bind fun res => .pure (res.1, history)

/-- Decryption refuses every ciphertext recorded in the challenge history. -/
theorem adaptiveIndImpl_dec_issued (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
    (history : List (Fin (S.ctLen.eval n) → Bool))
    (hc : cast (S.indSpec_decDom n) c ∈ history) :
    S.adaptiveIndImpl atk b n pk sk cap 0 c history = .pure (zeroBits _, history) := by
  rw [adaptiveIndImpl, if_pos hc]

/-- A challenge below the cap uses the single game's fresh challenge branch, then
adds that ciphertext to the history. -/
theorem adaptiveIndImpl_challenge_fresh (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (S.indImpl atk b n pk sk 1 mm none).bind
        (fun res => .pure (res.1, res.2.toList ++ history)) := by
  rw [adaptiveIndImpl, if_pos h]

/-- A fresh challenge samples an encryption tape, returns the selected encryption, and
prepends exactly that ciphertext to the history.

**Proof sketch.** Read the original game's first-challenge equation on the specification's
type, then simplify the continuation that saves the returned ciphertext. -/
theorem adaptiveIndImpl_challenge_encrypt (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (c, c :: history) := by
  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk cap mm history h,
    S.indImpl_challenge_none_onSpec, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, Option.toList_some, List.singleton_append]

/-- A positive cap of one issues a fresh first challenge, as in Definition 171.5. -/
private theorem adaptiveIndImpl_one_empty (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
    S.adaptiveIndImpl atk b n pk sk 1 1 mm [] =
      (S.indImpl atk b n pk sk 1 mm none).bind (fun res => .pure (res.1, res.2.toList)) := by
  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk 1 mm []
    (by simp only [List.length_nil, Nat.zero_lt_one])]
  simp only [List.append_nil]

/-- At a full challenge cap, repeat the latest ciphertext without adding to the history. -/
theorem adaptiveIndImpl_challenge_full (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : cap ≤ history.length)
    (c : Fin (S.ctLen.eval n) → Bool) (hc : history.head? = some c) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (S.indImpl atk b n pk sk 1 mm (some c)).bind
        (fun res => .pure (res.1, history)) := by
  rw [adaptiveIndImpl, if_neg (Nat.not_lt_of_ge h), hc]

/-- A zero challenge cap keeps the initial history empty and returns the zero reply. -/
theorem adaptiveIndImpl_challenge_zero (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
    S.adaptiveIndImpl atk b n pk sk 0 1 mm [] = .pure (zeroBits _, []) := by
  rw [adaptiveIndImpl, if_neg (Nat.not_lt_zero _)]
  rfl

/-- Decryption outside the history uses the original oracle's availability and decoding
rules. Its answer leaves the full history unchanged. -/
theorem adaptiveIndImpl_dec_other (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
    (history : List (Fin (S.ctLen.eval n) → Bool))
    (hc : cast (S.indSpec_decDom n) c ∉ history) :
    S.adaptiveIndImpl atk b n pk sk cap 0 c history =
      (S.indImpl atk b n pk sk 0 c history.head?).bind (fun res => .pure (res.1, history)) := by
  rw [adaptiveIndImpl, if_neg hc]

/-- At cap one, each oracle call agrees with the old game when the optional challenge is
represented as a list.

**Proof sketch.** Split by oracle and old challenge state. For decryption the
single-game state is preserved. A fresh challenge creates one list entry, and a repeat
returns the same state. -/
theorem adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (i : Fin 2) (x : (S.indSpec n).dom i) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.adaptiveIndImpl atk b n pk sk 1 i x s.toList =
      (S.indImpl atk b n pk sk i x s).bind (fun res => .pure (res.1, res.2.toList)) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
  rcases hi with rfl | rfl
  · cases s with
    | none =>
      rw [Option.toList_none, S.adaptiveIndImpl_dec_other atk b n pk sk 1 x []
        List.not_mem_nil, List.head?_nil, S.indImpl_dec_onSpec]
      split <;> simp only [OracleComp.pure_bind, Option.toList_none]
    | some c =>
      by_cases h : cast (S.indSpec_decDom n) x = c
      · rw [S.adaptiveIndImpl_dec_issued atk b n pk sk 1 x (some c).toList (by
          simp only [Option.toList_some, List.mem_singleton]; exact h)]
        rw [S.indImpl_dec_onSpec, h]
        simp
      · rw [S.adaptiveIndImpl_dec_other atk b n pk sk 1 x (some c).toList (by
          simp only [Option.toList_some, List.mem_singleton]; exact h)]
        simp only [Option.toList_some, List.head?_cons, S.indImpl_dec_onSpec]
        split <;> simp only [OracleComp.pure_bind, Option.toList_some]
  · cases s with
    | none => exact S.adaptiveIndImpl_one_empty atk b n pk sk x
    | some c =>
      rw [S.adaptiveIndImpl_challenge_full atk b n pk sk 1 x (some c).toList (by simp) c (by simp),
        S.indImpl_challenge_repeat_onSpec]
      simp only [OracleComp.pure_bind]

/-- Cap-one simulation is the single-challenge simulation with its final state encoded
as a list.

**Proof sketch.** Induct over the adversary's query tree and apply the per-call equality. -/
theorem simulate_adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    {α : Type} (t : OracleComp (S.indSpec n) α) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    simulate (S.adaptiveIndImpl atk b n pk sk 1) t s.toList =
      (simulate (S.indImpl atk b n pk sk) t s).bind
        (fun res => .pure (res.1, res.2.toList)) := by
  induction t generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, S.adaptiveIndImpl_one, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext res
    exact ih res.1 res.2

/-- The left-or-right game uses one key and hidden bit across the adaptive queries. -/
noncomputable def adaptiveIndGame (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) cap)
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
    fun res => .pure (res.1 0)

/-- The experiment's only sampled keys come from one activation of key generation. -/
theorem adaptiveIndGame_eq (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame atk A q cap b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) cap)
          (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
        fun res => .pure (res.1 0) := rfl

/-- The cap-one experiment and the existing single-challenge experiment return the same bit
on the same sampled generator and adversary tapes.

**Proof sketch.** Fix both sampled tapes and apply the simulation correspondence.
Both experiments read the same bit of the simulation's result. -/
theorem adaptiveIndGame_one (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame atk A q 1 b n = S.indGame atk A q b n := by
  simp only [S.adaptiveIndGame_eq, S.indGame_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [← Option.toList_none (α := Fin (S.ctLen.eval n) → Bool), S.simulate_adaptiveIndImpl_one,
    OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- The adversary's left-or-right advantage is negligible for polynomial total and
challenge budgets. The first catalog witnesses will have message length equal to the
security parameter. -/
def AdaptiveINDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
      (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n

/-- The adaptive predicate quantifies over both the total query and challenge budgets. -/
theorem adaptiveINDSecure_iff (atk : Attack) :
    S.AdaptiveINDSecure atk ↔
      ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
        advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
          (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n :=
  Iff.rfl

/-- Adaptive security entails security in the original game.

**Proof sketch.** Use the constant cap one and the exact simulation equation. -/
theorem AdaptiveINDSecure.single {atk : Attack} (h : S.AdaptiveINDSecure atk) :
    S.INDSecure atk := by
  rw [S.adaptiveINDSecure_iff] at h
  rw [S.INDSecure_iff]
  intro A q
  obtain ⟨ε, hε, hb⟩ := h A q (.const 1)
  refine ⟨ε, hε, fun n => ?_⟩
  simpa only [PolyExpr.eval_const, S.adaptiveIndGame_one] using hb n

end TCSlib.Cryptography.Composability.FixedLengthPKScheme
