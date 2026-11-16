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
# The composition theorem: Alice's side

Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
Alice's real and ideal samples of `H.compose ρ`. On the `main`-tapes `m`, a run word `V j` per
call and the sample `sampleA m V` (the assembled view of `V`, her input, her `main`-tape and the
hybrid main phase, paired with Bob's output in `main`):
1. under `GoodRuns` the real sample is `sampleA m (real views)` (`realA_compose_sampleA`); the
   bad event has probability at most `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
2. the hybrid argument replaces the real views by `ρ`'s simulator, at most `ε₂(n)` per run
   (`exists_gapA`: the reduction `exists_gap_le` with a polynomially long template,
   `exists_tmplA_bound`; `abs_chain_le`);
3. `sampleA m (simulated views)` is `D ∘ Φ` on the hybrid real sample, and `D` on the simulator
   `S_A` is `D ∘ Φ` on the hybrid ideal sample (`acceptProb_realA_dPhi`, `acceptProb_post_pre`),
   so `H.HBCSecure F` bounds the rest (`exists_simA`).

## Main definitions

* `HybridProtocol.viewRunA`, `simRunA`: Alice's real and simulated run words.
* `HybridProtocol.sampleA`: Alice's sample from run words.

## Main results

* `HybridProtocol.realA_compose_sampleA`, `exists_tmplA_bound`, `exists_gapA`,
  `acceptProb_realA_dPhi`.
* `HybridProtocol.exists_simA`: Alice's side of `hbcSecure_compose`.

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

/-- **Alice's real run word** for call `j`: her encoded view of `ρ` on the call inputs
`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
def viewRunA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
  (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
    (H.inB n ys (List.ofFn m.2) j) t).encode

/-- The defining equation of `viewRunA` (see `viewRunA`).
`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
theorem viewRunA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunA ρ n xs ys m j t =
      (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl

/-- **Alice's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on her call
input and her ideal answer `⟦f_A(callA_j, callB_j)⟧`, with coins `s`.
`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
def simRunA (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (s : S.Coins n) : List Bool :=
  S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s

/-- The defining equation of `simRunA` (see `simRunA`).
`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
theorem simRunA_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
    H.simRunA S n xs ys m j s =
      S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1))
        s := rfl

/-- **Alice's sample from run words**: the assembled view (`asmView` with `ρ.P`'s coins, Bob's
moves read, no leading filler) of the words `V`, her input `xs`, her `main`-tape and the hybrid
main phase on the ideal answers, paired with Bob's output in that hybrid execution.
`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn
m.2)) m).1) V) (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
def sampleA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
  pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0 (List.replicate n true)
      xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
        (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
    (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)

/-- The defining equation of `sampleA` (see `sampleA`).
`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn
m.2)) m).1) V) (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
theorem sampleA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
    H.sampleA ρ n xs ys m V =
      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
          (List.replicate n true) xs (List.ofFn m.1)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl

/-- **The real sample under `GoodRuns`** (step 2):
`F.realA (H.compose ρ) n x y (composeCoins (m, t)) = sampleA m (j ↦ viewRunA m j (t j))`
(`realA_compose_eq`, `realViewA_eq`). -/
theorem realA_compose_sampleA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      H.sampleA ρ n (List.ofFn x) (List.ofFn y) m fun j =>
        if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
          (t ⟨j, h⟩) else [] := by
  have hV : H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
      if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
        (t ⟨j, h⟩) else [] :=
    funext fun j => by rw [realViewA_eq]; rfl
  rw [H.realA_compose_eq ρ hM n x y m t hg, hV, sampleA_eq]

/-- **The templates of Alice's hybrid steps are polynomially long**: for some polynomial `q`, for
all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
`⟨⟨1^n, ⟦x⟧⟩, ⟨⟦m.1⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
Bob's output in `main` has at most `q(n)` bits.
`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
S.Coins n)), (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn x)) (pairEncode
(List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n
(List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n (List.ofFn x) (List.ofFn
y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1))) ((List.range i).map (hybV (H.viewRunA ρ n
(List.ofFn x) (List.ofFn y)) (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a)) ((List.range
(H.calls.eval n - (i + 1))).map fun k => hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
(H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)) (H.main.outV H.main.P (List.replicate n
true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n
(List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤ q.eval n`.

**Proof sketch.** The main phase and Bob's output are polynomially long (`exists_main_msgs_le`,
`exists_main_outV_le`); every run word is a real view (`exists_viewP_le`), a simulator output on
an argument of `2 G.inA(n) + 2 + G.outA(n)` bits (`exists_runAt_le`) or empty; at most `L(n)` of
them are encoded (`length_encodeMsgs_le`); the rest is `length_pairEncode`. -/
theorem exists_tmplA_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
    (S : NUPPT) :
    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
        ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
          (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))
        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
          hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
        q.eval n := by
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  obtain ⟨O, hO⟩ := H.exists_main_outV_le hH
  obtain ⟨V, hV⟩ := exists_viewP_le hρ
  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inA) (.const 2)) G.outA)
  -- every run word has at most `V(n) + Sv(n)` bits
  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (j : ℕ),
      (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
    intro n x y i a j
    rw [hybV_eq]
    split_ifs with h₁ h₂
    · rw [simRunA_eq]
      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
      rw [length_pairEncode, inA_val, List.length_ofFn, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
    · rw [viewRunA_eq, inA_val, inB_val]
      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
    · exact Nat.zero_le _
  -- the encoded word lists
  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
      (Strategy.encodeMsgs (l.map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
      fun n x y i a l hl => ?_⟩
    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
      exact hw n x y i a j
    · rw [List.length_map]
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.mul_le_mul_right _ hl
  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
    F.inA)) (.const 2)) (.add (.add (.mul (.const 2) H.main.P.coins) (.const 2)) E)
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
      hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
      (by rw [List.length_map, List.length_range]; omega)
    rwa [List.map_map] at h
  have h₃ := (hE n x y a.1).1
  have h₄ := hO n x y a.1
  have hc : (List.ofFn a.1.1).length = H.main.P.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  have hu : (List.replicate n true).length = n := List.length_replicate
  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Alice's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT
`D` there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
`|Pr_t[D(sampleA a.1 (plugV i a (viewRunA a.1 i t)))] −
Pr_s[D(sampleA a.1 (plugV i a (simRunA a.1 i s)))]| ≤ ε₂(n)`.

**Proof sketch.** `exists_gap_le` with `ρ`'s Alice-side samplers, the instances
`(x, y, i, a)`, the call inputs of `a.1` at `i`, and the template of `exists_tmplA_bound`. The
filled template is the sample: `asmW_pairEncode`, `msgAt_encodeMsgs` and `getD_plug` turn it into
`asmView` of `plugV`, and the first component of `ρ`'s real (ideal) sample is the real
(simulated) run word (`Functionality.realA_eq`, `idealA_eq`, `inA_val`, `inB_val`). -/
theorem exists_gapA {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realA ρ n x y) (G.idealA S n x y) (D.distinguisherL n) ≤ ε n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      |acceptProb (fun t => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
            (H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
        acceptProb (fun s => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
            (H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
        ε₂ n := by
  obtain ⟨q, hq⟩ := H.exists_tmplA_bound ρ hH hρ S
  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
    (Sc := fun n => S.Coins n) (fun n => G.realA ρ n) (fun n => G.idealA S n) hS H.calls
    ρ.rounds ρ.P.coins ρ.verifierFirst true 0
    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
      Fin (H.calls.eval n) ×
      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.1))
      (pairEncode (List.ofFn θ.2.2.2.1.1) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true)
        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2))
        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).1)))
    (fun n θ => H.main.outV H.main.P (List.replicate n true)
      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2))
      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
      (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
      hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
        (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
  -- the filled template is the sample with run `i` replaced
  have hfill : ∀ v : List Bool, H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
      (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a v) =
      pairEncode (asmW H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x)
            (List.ofFn y)) (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a) ++
            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
              hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
                (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
    intro v
    rw [sampleA_eq, asmW_pairEncode]
    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
    rw [List.length_replicate] at hj
    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
  have hreal : ∀ t, H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
      pairFstD (G.realA ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
    rw [Functionality.realA_eq, pairFstD_pairEncode, viewRunA_eq, inA_val, inB_val]
  have hsim : ∀ s, H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s =
      pairFstD (G.idealA S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
    rw [Functionality.idealA_eq, pairFstD_pairEncode, simRunA_eq, inA_val]
  simp only [hfill, hreal, hsim]
  exact h n (x, y, i, a)

/-- **The simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
reduction of `exists_dPhi` (coins `calls · S.coins + D.coins`), then
`Pr[DΦ(H.realA F n x y)] = Pr_{(m, s)}[D(sampleA m (j ↦ simRunA m j (s j)))]`.

**Proof sketch.** Unfold `DΦ` (`acceptProb_pre`) and read its extra coins as one block of
`S.coins(n)` bits per call (`blocksCoins`). On `H.realA`, `phiD` keeps Bob's output and applies
`phiV` to Alice's view of `main`, whose private input is `⟨⟦x⟧, answers⟩` (`phiD_pairEncode`,
`phiV_view`): run `j` is `S`'s output on the call input (`hcall`, `inA_val`), the `j`-th
answer block (`coinBlock_flatten`) and the `j`-th coin block (`coinBlock_blocksCoins`), i.e.
`simRunA` (`NUPPT.runAtL_eq_output_layout`). -/
theorem acceptProb_realA_dPhi {F : Functionality} (S D DΦ : NUPPT) {fA : List Bool → List Bool}
    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
      fA (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
    (hD : ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    acceptProb (H.realA F n x y) (DΦ.distinguisherL n) =
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunA S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  rw [acceptProb_pre (H.realA F n x y) DΦ D (.mul H.calls S.coins) n
    (fun w e => phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
    (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  show phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
        (pairEncode (H.realA F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
  rw [realA_eq, phiD_pairEncode, Protocol.viewP_eq, View.encode_mk, privA_eq, phiV_view,
    sampleA_eq, privA_eq, Protocol.transcript_eq_transcriptWith]
  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
  rw [List.length_replicate] at hj
  rw [dif_pos hj, simRunA_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
    hcall n (List.ofFn x) (List.ofFn z.1.1) ⟨j, hj⟩, inA_val, ← NUPPT.coinLen_eq,
    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersA_eq,
    coinBlock_flatten _ (fun c hc' => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]

/-- **Alice's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there
is a non-uniform PPT `S_A` such that every non-uniform PPT `D` has a negligible `ε` with
`distAdv (F.realA (H.compose ρ) n x y) (F.idealA S_A n x y) D ≤ ε(n)` for all `n`, `x`, `y`.

**Proof sketch.** `S_A` post-processes the hybrid simulator by `Φ` (`exists_simulator`). For `D`:
1. relabel the coins (`composeCoins`); the real sample is `sampleA` of the real views except
   on `¬ GoodRuns` (`realA_compose_sampleA`, `distAdv_le_uprob_of_eq`), of probability at most
   `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
2. the real and simulated views are within `L(n) ε₂(n)` (`abs_chain_le`, `exists_gapA`);
3. `D` on the simulated views is `DΦ` on `H.realA` (`acceptProb_realA_dPhi`), and `D` on
   `S_A` is `DΦ` on `S_A^H` (`acceptProb_post_pre`, `phiD_pairEncode`), so `H.HBCSecure F`
   bounds this distance by `ε₃(n)`.
The total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` is negligible (`negligible_polyExpr_mul`). -/
theorem exists_simA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
    ∃ SA : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realA (H.compose ρ) n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n := by
  obtain ⟨hHpt, SH, SHB, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
  obtain ⟨-, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
  obtain ⟨SA, hSAc, hSA⟩ := exists_simulator SρA H.calls ρ.rounds ρ.P.coins G.outA
    ρ.verifierFirst true 0 SH hfA
  refine ⟨SA, fun D => ?_⟩
  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapA ρ hHpt hρpt SρA (fun D => by
    obtain ⟨ε, hε, h⟩ := hρs D
    exact ⟨ε, hε, fun n x y => (h n x y).1⟩) D
  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst
    true 0 D hfA
  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
    fun n x y => ?_⟩
  -- step 1: the statistical switch
  have s1 : |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realA (H.compose ρ) n x y)]
    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
      (fun z hz => H.realA_compose_sampleA ρ hM n x y z.1 z.2 (not_not.1 hz))
    rw [distAdv_def] at h
    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
  -- step 2: the hybrid argument over the runs
  have s2 := abs_chain_le (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
    (H.simRunA SρA n (List.ofFn x) (List.ofFn y)) (H.sampleA ρ n (List.ofFn x) (List.ofFn y))
    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
  -- step 3: the hybrid model
  have hid : ∀ S : NUPPT, F.idealA S n x y = fun s =>
      pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
        (List.ofFn (F.f n x y).2) := fun S => funext (Functionality.idealA_eq F S n x y)
  have e3 : acceptProb (F.idealA SA n x y) (D.distinguisherL n) =
      acceptProb (F.idealA SH n x y) (DΦ.distinguisherL n) := by
    rw [hid SA, hid SH]
    exact acceptProb_post_pre SA SH DΦ D (.mul H.calls SρA.coins) n
      (fun hv e => phiV SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode hv e)))
      (fun w e => phiD SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode w e)))
      (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) (List.ofFn (F.f n x y).2) hSAc
      (hSA n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
      acceptProb (F.idealA SA n x y) (D.distinguisherL n)| ≤ ε₃ n := by
    rw [← H.acceptProb_realA_dPhi ρ SρA D DΦ hcallA hDΦc hDΦ n x y, e3]
    have h := (h₃ n x y).1
    rwa [distAdv_def] at h
  rw [distAdv_def]
  calc |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
        acceptProb (F.idealA SA n x y) (D.distinguisherL n)|
      ≤ |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (F.idealA SA n x y) (D.distinguisherL n)| :=
        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
