/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.HardcoreBit.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correct answers of the runs

Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. The
output clause of honest-but-curious security makes a secure protocol correct: a distinguisher
that compares the other party's output in the sample with the ideal output on the worst-case
inputs of length `n`, given as advice, shows that each party's output differs from its ideal
output with negligible probability, uniformly over the inputs (`ComposeProb.exists_correct`).
By the union bound over the calls, every run of the composed protocol gives the ideal answers
except with probability `L(n)` times that bound (`HybridProtocol.uprob_not_goodRuns_le`).

## Main results

* `ComposeProb.exists_correct`: a secure protocol computes its functionality except with
  negligible probability.
* `HybridProtocol.inA_val`, `inB_val`: the call inputs at a call index.
* `HybridProtocol.uprob_not_goodRuns_le`: the bad event of the statistical switch.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography

namespace ComposeProb

/-- **A secure protocol computes its functionality** (the output clause of [PS10,
Definition 155.1]): if `ρ` has simulators `S_A`, `S_B` against every non-uniform PPT
distinguisher, there is a negligible `ε_c` with, for all `n` and all inputs `x`, `y` of `G`'s
lengths, `Pr_t[ρ.outP ≠ ⟦f_A(x, y)⟧ ∨ ρ.outV ≠ ⟦f_B(x, y)⟧] ≤ ε_c(n)` on common input `1^n`.

**Proof sketch.** For Alice's output take the inputs `w_n` maximizing
`Pr_t[outP ≠ ⟦f_A⟧]` at each `n`, and the test machine accepting when the second component of
its sample is `⟦f_A(w_n)⟧` (`exists_test`; advice of `G.outA(n)` bits). On Bob's ideal sample
at `w_n` it accepts with probability `1` (the second component is `⟦f_A(w_n)⟧`); on the real one
with `Pr_t[outP = ⟦f_A(w_n)⟧]` (`acceptProb_test`). So `Pr_t[outP ≠ ⟦f_A⟧] ≤
Pr_t[outP(w_n) ≠ ⟦f_A(w_n)⟧] = 1 − Pr_t[outP(w_n) = ⟦f_A(w_n)⟧] ≤ ε_A(n)` (`uprob_not`).
Likewise for Bob's output on Alice's side; take `ε_c = ε_A + ε_B` (`uprob_or_le`). -/
theorem exists_correct {G : Functionality} {ρ : Protocol} (SA SB : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realA ρ n x y) (G.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (G.realB ρ n x y) (G.idealB SB n x y) (D.distinguisherL n) ≤ ε n) :
    ∃ εc : ℕ → ℝ, Negligible εc ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        uprob (fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
          ρ.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) t ≠
              List.ofFn (G.f n x y).1 ∨
            ρ.outV ρ.P (List.replicate n true) (List.ofFn x) (List.ofFn y) t ≠
              List.ofFn (G.f n x y).2) ≤ εc n := by
  -- the worst-case inputs for each output
  have hmax : ∀ (n : ℕ) (q : (Fin (G.inA.eval n) → Bool) × (Fin (G.inB.eval n) → Bool) → ℝ),
      ∃ w, ∀ w', q w' ≤ q w := fun n q => by
    obtain ⟨w, -, hw⟩ := exists_max_image univ q univ_nonempty
    exact ⟨w, fun w' => hw w' (mem_univ w')⟩
  choose wA hwA using fun n => hmax n fun w => uprob fun t : ρ.ExecCoins ρ.P
    (List.replicate n true) => ρ.outP (List.replicate n true) (List.ofFn w.1) (List.ofFn w.2) t ≠
      List.ofFn (G.f n w.1 w.2).1
  choose wB hwB using fun n => hmax n fun w => uprob fun t : ρ.ExecCoins ρ.P
    (List.replicate n true) => ρ.outV ρ.P (List.replicate n true) (List.ofFn w.1)
      (List.ofFn w.2) t ≠ List.ofFn (G.f n w.1 w.2).2
  obtain ⟨BA, hBA⟩ := exists_test (fun n => List.ofFn (G.f n (wA n).1 (wA n).2).1) G.outA
    fun n => by rw [List.length_ofFn]
  obtain ⟨BB, hBB⟩ := exists_test (fun n => List.ofFn (G.f n (wB n).1 (wB n).2).2) G.outB
    fun n => by rw [List.length_ofFn]
  obtain ⟨εA, hεA, hA⟩ := hS BA
  obtain ⟨εB, hεB, hB⟩ := hS BB
  refine ⟨fun n => εA n + εB n, hεA.add hεB, fun n x y => (uprob_or_le _ _).trans
    (add_le_add ((hwA n (x, y)).trans ?_) ((hwB n (x, y)).trans ?_))⟩
  · -- Alice's output, through Bob's samples
    have h1 : acceptProb (G.realB ρ n (wA n).1 (wA n).2) (BA.distinguisherL n) =
        uprob fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
          ρ.outP (List.replicate n true) (List.ofFn (wA n).1) (List.ofFn (wA n).2) t =
            List.ofFn (G.f n (wA n).1 (wA n).2).1 := by
      rw [acceptProb_test _ BA n _ (hBA n)]
      simp only [Functionality.realB_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_eq_true_iff]
    have h2 : acceptProb (G.idealB SB n (wA n).1 (wA n).2) (BA.distinguisherL n) = 1 := by
      rw [acceptProb_test _ BA n _ (hBA n)]
      simp only [Functionality.idealB_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_true]
      exact uprob_true
    have h3 := (hA n (wA n).1 (wA n).2).2
    rw [distAdv_def, h1, h2, abs_le] at h3
    have h4 := uprob_not fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
      ρ.outP (List.replicate n true) (List.ofFn (wA n).1) (List.ofFn (wA n).2) t =
        List.ofFn (G.f n (wA n).1 (wA n).2).1
    exact (le_of_eq h4).trans (by linarith [h3.1])
  · -- Bob's output, through Alice's samples
    have h1 : acceptProb (G.realA ρ n (wB n).1 (wB n).2) (BB.distinguisherL n) =
        uprob fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
          ρ.outV ρ.P (List.replicate n true) (List.ofFn (wB n).1) (List.ofFn (wB n).2) t =
            List.ofFn (G.f n (wB n).1 (wB n).2).2 := by
      rw [acceptProb_test _ BB n _ (hBB n)]
      simp only [Functionality.realA_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_eq_true_iff]
    have h2 : acceptProb (G.idealA SA n (wB n).1 (wB n).2) (BB.distinguisherL n) = 1 := by
      rw [acceptProb_test _ BB n _ (hBB n)]
      simp only [Functionality.idealA_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_true]
      exact uprob_true
    have h3 := (hB n (wB n).1 (wB n).2).1
    rw [distAdv_def, h1, h2, abs_le] at h3
    have h4 := uprob_not fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
      ρ.outV ρ.P (List.replicate n true) (List.ofFn (wB n).1) (List.ofFn (wB n).2) t =
        List.ofFn (G.f n (wB n).1 (wB n).2).2
    exact (le_of_eq h4).trans (by linarith [h3.1])

end ComposeProb

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- Alice's input to a call `j : Fin calls(n)` is `⟦callA(n, zA, rA, j)⟧` (`inA_eq`).
`H.inA n zA rA j = List.ofFn (H.callA n zA rA j)`. -/
theorem inA_val (n : ℕ) (zA rA : List Bool) (j : Fin (H.calls.eval n)) :
    H.inA n zA rA j = List.ofFn (H.callA n zA rA j) := by
  rw [inA_eq, dif_pos j.2]

/-- Bob's input to a call `j : Fin calls(n)` is `⟦callB(n, zB, rB, j)⟧` (`inB_eq`).
`H.inB n zB rB j = List.ofFn (H.callB n zB rB j)`. -/
theorem inB_val (n : ℕ) (zB rB : List Bool) (j : Fin (H.calls.eval n)) :
    H.inB n zB rB j = List.ofFn (H.callB n zB rB j) := by
  rw [inB_eq, dif_pos j.2]

/-- **The bad event of the statistical switch**: if on common input `1^n` every pair of inputs of
`G`'s lengths makes a party's `ρ`-output wrong with probability at most `ε_c`, then over the
`main`-tapes and the run tapes some run gives a wrong answer with probability at most
`calls(n) · ε_c`.
`uprob (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) => ¬
H.GoodRuns ρ n zA zB z.1 z.2) ≤ H.calls.eval n * εc`.

**Proof sketch.** `¬ GoodRuns` is the union over the calls `j` of the event that run `j`'s
outputs are wrong (`goodRuns_iff`; `uprob_exists_le`). For fixed `main`-tapes `m` that event
concerns the run tapes `t j` only, on the call inputs of `m`, which have `G`'s lengths
(`inA_val`, `inB_val`): its probability is at most `ε_c` (`HardcoreBit.pushesUniform_eval`),
hence so is its average over `m` (`uprob_prod`, `HardcoreBit.uexp_mono`,
`HardcoreBit.uexp_const`). -/
theorem uprob_not_goodRuns_le (n : ℕ) (zA zB : List Bool) (εc : ℝ)
    (hc : ∀ (xA : Fin (G.inA.eval n) → Bool) (yB : Fin (G.inB.eval n) → Bool),
      uprob (fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
        ρ.outP (List.replicate n true) (List.ofFn xA) (List.ofFn yB) t ≠
            List.ofFn (G.f n xA yB).1 ∨
          ρ.outV ρ.P (List.replicate n true) (List.ofFn xA) (List.ofFn yB) t ≠
            List.ofFn (G.f n xA yB).2) ≤ εc) :
    uprob (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
      ¬ H.GoodRuns ρ n zA zB z.1 z.2) ≤ H.calls.eval n * εc := by
  -- the event that run `j` is wrong, on the run tape `t'`
  let bad : H.Coins n → Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) → Prop :=
    fun m j t' =>
      ρ.outP (List.replicate n true) (List.ofFn (H.callA n zA (List.ofFn m.1) j))
          (List.ofFn (H.callB n zB (List.ofFn m.2) j)) t' ≠
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∨
      ρ.outV ρ.P (List.replicate n true) (List.ofFn (H.callA n zA (List.ofFn m.1) j))
          (List.ofFn (H.callB n zB (List.ofFn m.2) j)) t' ≠
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
  have hsub : ∀ z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)),
      ¬ H.GoodRuns ρ n zA zB z.1 z.2 → ∃ j ∈ (univ : Finset (Fin (H.calls.eval n))),
        bad z.1 j (z.2 j) := by
    intro z hz
    rw [goodRuns_iff] at hz
    push_neg at hz
    obtain ⟨j, hj⟩ := hz
    refine ⟨j, mem_univ j, ?_⟩
    show _ ∨ _
    rw [← H.inA_val n zA (List.ofFn z.1.1) j, ← H.inB_val n zB (List.ofFn z.1.2) j]
    by_cases h : ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn z.1.1) j)
        (H.inB n zB (List.ofFn z.1.2) j) (z.2 j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn z.1.1) j) (H.callB n zB (List.ofFn z.1.2) j)).1
    · exact Or.inr (hj h)
    · exact Or.inl h
  calc uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
        ρ.ExecCoins ρ.P (List.replicate n true)) => ¬ H.GoodRuns ρ n zA zB z.1 z.2)
      ≤ uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) => ∃ j ∈ univ, bad z.1 j (z.2 j)) :=
        uprob_mono hsub
    _ ≤ ∑ j ∈ (univ : Finset (Fin (H.calls.eval n))),
          uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) => bad z.1 j (z.2 j)) :=
        uprob_exists_le _ _
    _ ≤ ∑ _j ∈ (univ : Finset (Fin (H.calls.eval n))), εc := sum_le_sum fun j _ => by
        rw [uprob_prod]
        refine (HardcoreBit.uexp_mono fun m => ?_).trans_eq (HardcoreBit.uexp_const (εc))
        rw [(HardcoreBit.pushesUniform_eval j).uprob_eq (bad m j)]
        exact hc _ _
    _ = H.calls.eval n * εc := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
