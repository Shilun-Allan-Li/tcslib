/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem: Bob's side

Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
Bob's real and ideal samples of `H.compose ρ`, as for Alice's (`ComposeSecurity/SideA.lean`). On
the `main`-tapes `m`, a run word `V j` per call and the sample `sampleB m V` (the assembled view of
`V`, his input, his `main`-tape, the leading fillers and the hybrid main phase, paired with
Alice's output in `main`):
1. under `GoodRuns` the real sample is `sampleB m (real views)` (`realB_compose_sampleB`);
2. the hybrid argument replaces his real views by `ρ`'s simulator (`exists_gapB`,
   `exists_tmplB_bound`, `abs_chain_le`);
3. `sampleB m (simulated views)` is `D ∘ Φ` on the hybrid real sample (`acceptProb_realB_dPhi`),
   and `H.HBCSecure F` bounds the rest (`exists_simB`).

## Main definitions

* `HybridProtocol.viewRunB`, `simRunB`: Bob's real and simulated run words.
* `HybridProtocol.sampleB`: Bob's sample from run words.

## Main results

* `HybridProtocol.realB_compose_sampleB`, `exists_tmplB_bound`, `exists_gapB`,
  `acceptProb_realB_dPhi`.
* `HybridProtocol.exists_simB`: Bob's side of `hbcSecure_compose`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
  ComposeBound

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Bob's real run word** for call `j`: his encoded view of `ρ` on the call inputs
`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
def viewRunB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
  (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
    (H.inB n ys (List.ofFn m.2) j) t).encode

/-- The defining equation of `viewRunB` (see `viewRunB`).
`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
theorem viewRunB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunB ρ n xs ys m j t =
      (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl

/-- **Bob's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on his call
input and his ideal answer `⟦f_B(callA_j, callB_j)⟧`, with coins `s`.
`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
def simRunB (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (s : S.Coins n) : List Bool :=
  S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s

/-- The defining equation of `simRunB` (see `simRunB`).
`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
theorem simRunB_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
    H.simRunB S n xs ys m j s =
      S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2))
        s := rfl

/-- **Bob's sample from run words**: the assembled view (`asmView` with `ρ.V`'s coins, Alice's
moves read, `lead` leading fillers) of the words `V`, his input `ys`, his `main`-tape and the
hybrid main phase on the ideal answers, paired with Alice's output in that hybrid execution.
`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys
(List.ofFn m.1) (List.ofFn m.2)) m).2) V) (H.main.outP (List.replicate n true) (H.privA n xs ys
(List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
def sampleB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
  pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
      (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
    (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)

/-- The defining equation of `sampleB` (see `sampleB`).
`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys
(List.ofFn m.1) (List.ofFn m.2)) m).2) V) (H.main.outP (List.replicate n true) (H.privA n xs ys
(List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
theorem sampleB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
    H.sampleB ρ n xs ys m V =
      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
          (List.replicate n true) ys (List.ofFn m.2)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
        (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl

/-- **Bob's real sample under `GoodRuns`** (step 2): `F.realB (H.compose ρ) n x y (composeCoins
(m, t)) = sampleB m (j ↦ viewRunB m j (t j))` (`realB_compose_eq`, `realViewB_eq`). -/
theorem realB_compose_sampleB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      H.sampleB ρ n (List.ofFn x) (List.ofFn y) m fun j =>
        if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
          (t ⟨j, h⟩) else [] := by
  have hV : H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
      if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
        (t ⟨j, h⟩) else [] :=
    funext fun j => by rw [realViewB_eq]; rfl
  rw [H.realB_compose_eq ρ hM n x y m t hg, hV, sampleB_eq]

/-- **The templates of Bob's hybrid steps are polynomially long**: for some polynomial `q`, for
all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
`⟨⟨1^n, ⟦y⟧⟩, ⟨⟦m.2⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
Alice's output in `main` has at most `q(n)` bits.
`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
S.Coins n)), (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn y)) (pairEncode
(List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n
(List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n (List.ofFn x) (List.ofFn
y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2))) ((List.range i).map (hybV (H.viewRunB ρ n
(List.ofFn x) (List.ofFn y)) (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a)) ((List.range
(H.calls.eval n - (i + 1))).map fun k => hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
(H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)) (H.main.outP (List.replicate n true)
(H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n (List.ofFn x)
(List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤ q.eval n`.

**Proof sketch.** As `exists_tmplA_bound`, with Bob's half of the main phase
(`exists_main_msgs_le`), Alice's output (`exists_main_outP_le`), Bob's views (`exists_viewV_le`)
and simulator outputs on arguments of `2 G.inB(n) + 2 + G.outB(n)` bits (`exists_runAt_le`). -/
theorem exists_tmplB_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
    (S : NUPPT) :
    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
        ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
          (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))
        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
          hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
        q.eval n := by
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  obtain ⟨O, hO⟩ := H.exists_main_outP_le hH
  obtain ⟨V, hV⟩ := exists_viewV_le hρ
  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inB) (.const 2)) G.outB)
  -- every run word has at most `V(n) + Sv(n)` bits
  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (j : ℕ),
      (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
    intro n x y i a j
    rw [hybV_eq]
    split_ifs with h₁ h₂
    · rw [simRunB_eq]
      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
      rw [length_pairEncode, inB_val, List.length_ofFn, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
    · rw [viewRunB_eq, inA_val, inB_val]
      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
    · exact Nat.zero_le _
  -- the encoded word lists
  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
      (Strategy.encodeMsgs (l.map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
      fun n x y i a l hl => ?_⟩
    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
      exact hw n x y i a j
    · rw [List.length_map]
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.mul_le_mul_right _ hl
  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
    F.inB)) (.const 2)) (.add (.add (.mul (.const 2) H.main.V.coins) (.const 2)) E)
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
      hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
      (by rw [List.length_map, List.length_range]; omega)
    rwa [List.map_map] at h
  have h₃ := (hE n x y a.1).2
  have h₄ := hO n x y a.1
  have hc : (List.ofFn a.1.2).length = H.main.V.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  have hu : (List.replicate n true).length = n := List.length_replicate
  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Bob's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT `D`
there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
`|Pr_t[D(sampleB a.1 (plugV i a (viewRunB a.1 i t)))] −
Pr_s[D(sampleB a.1 (plugV i a (simRunB a.1 i s)))]| ≤ ε₂(n)`.

**Proof sketch.** As `exists_gapA`: `exists_gap_le` with `ρ`'s Bob-side samplers and the
template of `exists_tmplB_bound`; the first component of `ρ`'s real (ideal) Bob sample is the
real (simulated) run word (`Functionality.realB_eq`, `idealB_eq`, `inA_val`, `inB_val`). -/
theorem exists_gapB {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realB ρ n x y) (G.idealB S n x y) (D.distinguisherL n) ≤ ε n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      |acceptProb (fun t => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
            (H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
        acceptProb (fun s => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
            (H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
        ε₂ n := by
  obtain ⟨q, hq⟩ := H.exists_tmplB_bound ρ hH hρ S
  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
    (Sc := fun n => S.Coins n) (fun n => G.realB ρ n) (fun n => G.idealB S n) hS H.calls
    ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
      Fin (H.calls.eval n) ×
      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.2.1))
      (pairEncode (List.ofFn θ.2.2.2.1.2) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true)
        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2))
        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).2)))
    (fun n θ => H.main.outP (List.replicate n true)
      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2))
      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
      (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
      hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
        (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
  -- the filled template is the sample with run `i` replaced
  have hfill : ∀ v : List Bool, H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
      (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a v) =
      pairEncode (asmW H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x)
            (List.ofFn y)) (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a) ++
            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
              hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
                (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
    intro v
    rw [sampleB_eq, asmW_pairEncode]
    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
    rw [List.length_replicate] at hj
    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
  have hreal : ∀ t, H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
      pairFstD (G.realB ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
    rw [Functionality.realB_eq, pairFstD_pairEncode, viewRunB_eq, inA_val, inB_val]
  have hsim : ∀ s, H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s =
      pairFstD (G.idealB S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
    rw [Functionality.idealB_eq, pairFstD_pairEncode, simRunB_eq, inB_val]
  simp only [hfill, hreal, hsim]
  exact h n (x, y, i, a)

/-- **Bob's simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
reduction of `exists_dPhi` for Bob's post-processing (coins `calls · S.coins + D.coins`), then
`Pr[DΦ(H.realB F n x y)] = Pr_{(m, s)}[D(sampleB m (j ↦ simRunB m j (s j)))]`.

**Proof sketch.** As `acceptProb_realA_dPhi`, with Bob's view of `main`, whose private input is
`⟨⟦y⟧, answers⟩`, his call inputs (`hcall`, `inB_val`) and his answer blocks. -/
theorem acceptProb_realB_dPhi {F : Functionality} (S D DΦ : NUPPT) {fB : List Bool → List Bool}
    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
      fB (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
    (hD : ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    acceptProb (H.realB F n x y) (DΦ.distinguisherL n) =
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunB S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  rw [acceptProb_pre (H.realB F n x y) DΦ D (.mul H.calls S.coins) n
    (fun w e => phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
    (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  show phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
        (pairEncode (H.realB F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
  rw [realB_eq, phiD_pairEncode, Protocol.viewV_eq, View.encode_mk, privB_eq, phiV_view,
    sampleB_eq, privB_eq, Protocol.transcript_eq_transcriptWith]
  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
  rw [List.length_replicate] at hj
  rw [dif_pos hj, simRunB_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
    hcall n (List.ofFn y) (List.ofFn z.1.2) ⟨j, hj⟩, inB_val, ← NUPPT.coinLen_eq,
    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersB_eq,
    coinBlock_flatten _ (fun c hc' => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]

/-- **Bob's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there is
a non-uniform PPT `S_B` such that every non-uniform PPT `D` has a negligible `ε` with
`distAdv (F.realB (H.compose ρ) n x y) (F.idealB S_B n x y) D ≤ ε(n)` for all `n`, `x`, `y`.

**Proof sketch.** As `exists_simA`, with Bob's simulator post-processed by Bob's `Φ`
(`exists_simulator` with `ρ.V`'s coins, Alice's moves read and `lead` fillers), his real sample
(`realB_compose_sampleB`), the same bad event, the hybrid argument over his views
(`exists_gapB`, `abs_chain_le`) and the hybrid model (`acceptProb_realB_dPhi`,
`acceptProb_post_pre`). -/
theorem exists_simB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
    ∃ SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realB (H.compose ρ) n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  obtain ⟨hHpt, SHA, SH, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
  obtain ⟨-, -, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
  obtain ⟨SB, hSBc, hSB⟩ := exists_simulator SρB H.calls ρ.rounds ρ.V.coins G.outB
    ρ.verifierFirst false H.lead SH hfB
  refine ⟨SB, fun D => ?_⟩
  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapB ρ hHpt hρpt SρB (fun D => by
    obtain ⟨ε, hε, h⟩ := hρs D
    exact ⟨ε, hε, fun n x y => (h n x y).2⟩) D
  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst
    false H.lead D hfB
  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
    fun n x y => ?_⟩
  -- step 1: the statistical switch
  have s1 : |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realB (H.compose ρ) n x y)]
    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
      (fun z hz => H.realB_compose_sampleB ρ hM n x y z.1 z.2 (not_not.1 hz))
    rw [distAdv_def] at h
    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
  -- step 2: the hybrid argument over the runs
  have s2 := abs_chain_le (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
    (H.simRunB SρB n (List.ofFn x) (List.ofFn y)) (H.sampleB ρ n (List.ofFn x) (List.ofFn y))
    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
  -- step 3: the hybrid model
  have hid : ∀ S : NUPPT, F.idealB S n x y = fun s =>
      pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
        (List.ofFn (F.f n x y).1) := fun S => funext (Functionality.idealB_eq F S n x y)
  have e3 : acceptProb (F.idealB SB n x y) (D.distinguisherL n) =
      acceptProb (F.idealB SH n x y) (DΦ.distinguisherL n) := by
    rw [hid SB, hid SH]
    exact acceptProb_post_pre SB SH DΦ D (.mul H.calls SρB.coins) n
      (fun hv e => phiV SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode hv e)))
      (fun w e => phiD SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode w e)))
      (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) (List.ofFn (F.f n x y).1) hSBc
      (hSB n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
      acceptProb (F.idealB SB n x y) (D.distinguisherL n)| ≤ ε₃ n := by
    rw [← H.acceptProb_realB_dPhi ρ SρB D DΦ hcallB hDΦc hDΦ n x y, e3]
    have h := (h₃ n x y).2
    rwa [distAdv_def] at h
  rw [distAdv_def]
  calc |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
        acceptProb (F.idealB SB n x y) (D.distinguisherL n)|
      ≤ |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (F.idealB SB n x y) (D.distinguisherL n)| :=
        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
