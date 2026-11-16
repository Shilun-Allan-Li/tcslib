/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial bounds on the words of the hybrid-step templates

The templates of the reductions of the composition theorem [Gol04, §7.3.1, proof of
Theorem 7.3.3] hold the hybrid main phase, the other party's output in `main`, real views of
`ρ` and simulator outputs. Each has a length bounded by a polynomial in `n`, uniformly over the
inputs and coins:
* the encoded messages of the main phase on the ideal answers (`H.PolyTime` bounds `main`'s
  messages for any answers of the hybrid lengths) and the parties' outputs in `main` (efficient
  strategies on a polynomially long layout);
* the encoded views of `ρ` on inputs of `G`'s lengths (`G.PolyTime ρ`);
* the outputs of a machine on polynomially long arguments.

## Main results

* `HybridProtocol.exists_main_msgs_le`, `exists_main_outV_le`, `exists_main_outP_le`.
* `ComposeBound.exists_viewP_le`, `exists_viewV_le`, `exists_runAt_le`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (Definition 26.8) and §4.4 (time complexity of interactive machines).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography ComposeBound

/-- A list of length `c` is the encoding of a `c`-bit string. -/
private theorem exists_ofFn_eq {c : ℕ} {l : List Bool} (h : l.length = c) :
    ∃ t : Fin c → Bool, List.ofFn t = l := by
  subst h
  exact ⟨fun i => l[i.1], List.ofFn_getElem l⟩

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G)

/-- Alice's ideal answers have `calls(n) · G.outA(n)` bits.
`(H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n`. -/
theorem length_answersA (n : ℕ) (x y rA rB : List Bool) :
    (H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n := by
  rw [answersA_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- Bob's ideal answers have `calls(n) · G.outB(n)` bits.
`(H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n`. -/
theorem length_answersB (n : ℕ) (x y rA rB : List Bool) :
    (H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n := by
  rw [answersB_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- **The encoded main phase is polynomially long**: for some polynomial `E`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, both halves of the encoded transcript of
`main` on the ideal answers have at most `E(n)` bits.
`∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n (List.ofFn x)
(List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn
m.1) (List.ofFn m.2)) m).1).length ≤ E.eval n ∧ (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
(H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2).length ≤ E.eval n`.

**Proof sketch.** The ideal answers are strings of the hybrid lengths (`length_answersA`,
`length_answersB`), so `H.PolyTime` bounds every message by `B(n)`; each half of the transcript
has at most `rounds(n)` messages (`length_transcriptWith_fst_le`), so its encoding has at most
`E(n) = rounds(n) (2B(n) + 2)` bits (`length_encodeMsgs_le`). -/
theorem exists_main_msgs_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1).length ≤
          E.eval n ∧
        (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2).length ≤
          E.eval n := by
  obtain ⟨-, -, -, -, B, hB⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  refine ⟨.mul H.main.rounds (.add (.mul (.const 2) B) (.const 2)), fun n x y m => ?_⟩
  obtain ⟨aA, haA⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outA.eval n)
    (l := H.answersA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.length_answersA n _ _ _ _)
  obtain ⟨aB, haB⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outB.eval n)
    (l := H.answersB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.length_answersB n _ _ _ _)
  have hmsg := hB n x y aA aB m
  rw [haA, haB, ← privA_eq, ← privB_eq, Protocol.transcript_eq_transcriptWith] at hmsg
  rw [Protocol.transcript_eq_transcriptWith]
  have h₁ := length_transcriptWith_fst_le H.main H.main.P (List.replicate n true)
    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
  have h₂ := length_transcriptWith_snd_le H.main H.main.P (List.replicate n true)
    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
  have hR : H.main.rounds.eval (List.replicate n true).length = H.main.rounds.eval n := by
    rw [List.length_replicate]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
  exact ⟨(length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_left _ hw)).trans
      (Nat.mul_le_mul_right _ (h₁.trans hR.le)),
    (length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_right _ hw)).trans
      (Nat.mul_le_mul_right _ (h₂.trans hR.le))⟩

/-- **Bob's output in `main` is polynomially long**: for some polynomial `O`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, Bob's output in the hybrid execution has at
most `O(n)` bits.
`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (H.main.outV H.main.P (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn
m.1) (List.ofFn m.2)) (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
m).length ≤ O.eval n`.

**Proof sketch.** The output is `main.V.next` on `1^n`, Bob's private input, the messages he
received and his `main`-tape (`Protocol.outV_eq`), at most `C (|layout| + 1)^c` bits
(`Efficient.length_next_le`). The layout's length (`length_ilayout`) is linear in `n`, in his
private input's `2 F.inB(n) + 2 + calls(n) G.outB(n)` bits (`length_answersB`), in the encoded
messages (`exists_main_msgs_le`) and in his coin length; take `O = C (I + 1)^c` for that linear
bound `I`. -/
theorem exists_main_outV_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (H.main.outV H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
        O.eval n := by
  obtain ⟨-, hV, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hV
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  -- the layout: `1^n`, Bob's private input, the main phase and his `main`-tape
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
      (.add (.add (.mul (.const 2) .var) (.const 2))
        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
          (.add (.add (.mul (.const 2) F.inB) (.const 2)) (.mul H.calls G.outB)))) (.const 2)) E)))
      (.const 2))) (.const 2)) H.main.V.coins
  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
  have hI : (GI.ilayout (List.replicate n true)
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
      (H.main.transcriptWith H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2
      (List.ofFn m.2)).length ≤ I.eval n := by
    have h₁ := (hE n x y m).2
    rw [Protocol.transcript_eq_transcriptWith] at h₁
    have hpB : (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
        2 * F.inB.eval n + 2 + H.calls.eval n * G.outB.eval n := by
      rw [privB_eq, length_pairEncode, H.length_answersB, List.length_ofFn]
    have hc : (List.ofFn m.2).length = H.main.V.coins.eval n := by
      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
    have hu : (List.replicate n true).length = n := List.length_replicate
    rw [length_ilayout, hpB, hc]
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  rw [Protocol.outV_eq]
  refine (hC _ _ _ _).trans ?_
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

/-- **Alice's output in `main` is polynomially long**: for some polynomial `O`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, Alice's output in the hybrid execution has
at most `O(n)` bits.
`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (H.main.outP (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
O.eval n`.

**Proof sketch.** As `exists_main_outV_le`, with `main.P.next` on her private input
(`length_answersA`), the messages she received and her `main`-tape (`Protocol.outP_eq`). -/
theorem exists_main_outP_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (H.main.outP (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
        O.eval n := by
  obtain ⟨hP, -, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hP
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
      (.add (.add (.mul (.const 2) .var) (.const 2))
        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
          (.add (.add (.mul (.const 2) F.inA) (.const 2)) (.mul H.calls G.outA)))) (.const 2)) E)))
      (.const 2))) (.const 2)) H.main.P.coins
  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
  have hI : (GI.ilayout (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
      (H.main.transcriptWith H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1
      (List.ofFn m.1)).length ≤ I.eval n := by
    have h₁ := (hE n x y m).1
    rw [Protocol.transcript_eq_transcriptWith] at h₁
    have hpA : (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
        2 * F.inA.eval n + 2 + H.calls.eval n * G.outA.eval n := by
      rw [privA_eq, length_pairEncode, H.length_answersA, List.length_ofFn]
    have hc : (List.ofFn m.1).length = H.main.P.coins.eval n := by
      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
    have hu : (List.replicate n true).length = n := List.length_replicate
    rw [length_ilayout, hpA, hc]
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  rw [Protocol.outP_eq]
  refine (hC _ _ _ _).trans ?_
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

end HybridProtocol

namespace ComposeBound

/-- **Alice's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
`1^n` and inputs of `G`'s lengths, `|encode (viewP)| ≤ V(n)`.

**Proof sketch.** The encoded view is `⟨⟨1^n, x⟩, ⟨tape, encodeMsgs received⟩⟩` (`View.encode_mk`,
`length_pairEncode`): her tape has `ρ.P.coins(n)` bits, and she receives at most `rounds(n)`
messages (`length_transcriptWith_fst_le`) of at most `B(n)` bits each, `B` the bound of
`G.PolyTime ρ` (`length_encodeMsgs_le`); the sum is linear in these. -/
theorem exists_viewP_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
      (ρ.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
        V.eval n := by
  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inA))
      (.const 2)) (.add (.add (.mul (.const 2) ρ.P.coins) (.const 2))
        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
  have h₁ := length_transcriptWith_fst_le ρ ρ.P (List.replicate n true) (List.ofFn x)
    (List.ofFn y) t
  have hb := hB n x y t
  rw [Protocol.transcript_eq_transcriptWith] at hb
  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
    hb w (List.mem_append_left _ hw)).trans (Nat.mul_le_mul_right _ h₁)
  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
    rw [List.length_replicate]
  rw [hR] at h₂
  have hu : (List.replicate n true).length = n := List.length_replicate
  have hz : (List.ofFn x).length = G.inA.eval n := List.length_ofFn
  have ht : (List.ofFn t.1).length = ρ.P.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  rw [Protocol.viewP_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
    ht]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Bob's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
`1^n` and inputs of `G`'s lengths, `|encode (viewV)| ≤ V(n)`.

**Proof sketch.** As `exists_viewP_le`, with `ρ.V`'s tape and the messages he receives
(`length_transcriptWith_snd_le`). -/
theorem exists_viewV_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
      (ρ.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
        V.eval n := by
  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inB))
      (.const 2)) (.add (.add (.mul (.const 2) ρ.V.coins) (.const 2))
        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
  have h₁ := length_transcriptWith_snd_le ρ ρ.P (List.replicate n true) (List.ofFn x)
    (List.ofFn y) t
  have hb := hB n x y t
  rw [Protocol.transcript_eq_transcriptWith] at hb
  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
    hb w (List.mem_append_right _ hw)).trans (Nat.mul_le_mul_right _ h₁)
  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
    rw [List.length_replicate]
  rw [hR] at h₂
  have hu : (List.replicate n true).length = n := List.length_replicate
  have hz : (List.ofFn y).length = G.inB.eval n := List.length_ofFn
  have ht : (List.ofFn t.2).length = ρ.V.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  rw [Protocol.viewV_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
    ht]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **A machine's outputs on polynomially long arguments are polynomially long**: for an `NUPPT`
`S` and a polynomial `k` there is a polynomial `O` with `|S.runAt n w s| ≤ O(n)` whenever
`|w| ≤ k(n)` (`length_runAt_le`, `NUPPT.advice_length`). -/
theorem exists_runAt_le (S : NUPPT) (k : PolyExpr) :
    ∃ O : PolyExpr, ∀ n (w : List Bool) (s : S.Coins n), w.length ≤ k.eval n →
      (S.runAt n w s).length ≤ O.eval n := by
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2)
    (.add (.add (.mul (.const 2) .var) (.const 2)) k)) (.const 2)) S.adv)) (.const 2)) S.coins
  refine ⟨.mul (.const S.Ct) (.pow (.add I (.const 1)) S.ct), fun n w s hw => ?_⟩
  refine (length_runAt_le S n w s).trans ?_
  have ha := S.advice_length n
  have hI : 2 * (2 * (2 * n + 2 + w.length) + 2 + (S.advice n).length) + 2 + S.coinLen n ≤
      I.eval n := by
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
      NUPPT.coinLen_eq]
    omega
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

end ComposeBound

end TCSlib.Cryptography.SecureComputation
