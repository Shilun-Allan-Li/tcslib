/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `PATH` is `NL`-hard

The reduction `Complexity.PathHard.red` of [AB09, Theorem 4.18] is implicitly logspace
computable: its output length is polynomial (`Complexity.PathHard.length_red_le`), and its
bit and length languages are decided by the query machine `Complexity.PathHard.A` (in bit
and length mode) with polynomially bounded registers (`Complexity.LogProg.arm_decides_poly`).
Together with the correctness of the reduction (`Complexity.PathHard.red_mem_iff`), every
language in `NL` reduces to the raw `PATH` language.

## Main results

* `Complexity.PathHard.query_halts` — the query machine answers the bit (length) queries.
* `Complexity.PathHard.implicitlyLogspaceComputable_red` — the reduction is implicitly
  logspace computable. [AB09, Theorem 4.18, the logspace computability of the reduction]
* `Complexity.pathRawLang_NLHard` — every language in `NL` logspace-reduces to the raw
  `PATH` language. [AB09, Theorem 4.18]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg Codec

variable (N : FinNDTM Bool) (c₀ : ℕ)

/-- The query languages of the reduction: bits (`mode = false`) and length (`mode = true`). -/
def qLang (mode : Bool) : Language Bool :=
  if mode then indexLang fun x i => i < (red N c₀ x).length
  else indexLang fun x i => (red N c₀ x).getD i false = true

/-- The register bound of the query machine on `y`. -/
def qBnd (y : List Bool) : ℕ := y.length + 8 * nV (codeK N) c₀ y.length ^ 2 + 8

/-- The radius scale is at most the exponent scale. -/
lemma c₀_le : c₀ ≤ codeK N * (c₀ + 1) := by
  have : 2 ≤ codeK N := by simp [Codec.codeK]
  nlinarith

/-- No index language contains a word that is not a pair. -/
lemma not_mem_indexLang_of_pairDecode {p : List Bool → ℕ → Prop} {y : List Bool}
    (h : pairDecode y = none) : y ∉ indexLang p := by
  rintro ⟨x, i, rfl, -⟩
  rw [pairDecode_pairEncode] at h
  cases h

/-- The answer of the walk is the query answer.

**Proof sketch.** `n = nV = 2 ^ E` by definition; the bit at `i` is `red_getD`, and the length
is `length_red`. -/
lemma wAns_eq (mode : Bool) (x : List Bool) (i : ℕ) :
    wAns N x mode (c₀ * ell x.length) (codeK N * (c₀ + 1) * ell x.length + (codeK N + 2)) i =
      MultiTapeTM.indicator (qLang N c₀ mode : Set (List Bool)) (pairEncode x (Nat.bits i)) := by
  have hn : nV (codeK N) c₀ x.length =
      2 ^ (codeK N * (c₀ + 1) * ell x.length + (codeK N + 2)) := rfl
  cases mode with
  | true =>
    simp only [qLang, if_true, indicator_indexLang_pairEncode, wAns, length_red, hn]
  | false =>
    simp only [qLang, Bool.false_eq_true, if_false, indicator_indexLang_pairEncode]
    have key : ∀ (c : Bool) (inst : Decidable (c = true)), @decide _ inst = c := by
      intro c inst; cases c <;> simp
    rw [key, red_getD, hn]
    simp only [wAns, Bool.false_eq_true, if_false]

/-- **The query machine answers the queries**: on every query `y`, the machine started with
clear registers answers membership in the query language, through register values at most
`bnd y`.

**Proof sketch.** A non-pair is rejected by the parse (`parse_run`), and is in no index
language. For `y = ⟨x, β⟩`, the setup (`setup_run`) computes `E`, `2n`, `2n²` and the cap
`4n²`; the width check (`check_decode_run`) rejects a non-canonical `β` (no query) or a `β`
wider than `bits (4n²)` (an index `i > 4n² ≥ |red x|`, answered `0` in both modes), and
otherwise decodes `i`; the walk (`walk_halt`) answers `wAns`, which is the query answer
(`wAns_eq`). Every register stays below `|y| + 8n² + 8` with `n` at most the vertex count
for `|y|` (`nV_mono`). -/
theorem query_halts (mode : Bool) (y : List Bool) :
    AHalt (A c₀ (codeK N * (c₀ + 1)) (codeK N + 2) mode) (orc N) y
      (GuardLe (A c₀ (codeK N * (c₀ + 1)) (codeK N + 2) mode) y (qBnd N c₀ y))
      (some .lenQ, fun _ => 0, none)
      (MultiTapeTM.indicator (qLang N c₀ mode : Set (List Bool)) y) := by
  set K := codeK N with hK
  set B := qBnd N c₀ y with hB
  have hBv : B = y.length + 8 * nV K c₀ y.length ^ 2 + 8 := by simp only [hB, qBnd, ← hK]
  have hyB : y.length ≤ B := by omega
  rw [St.toV_zero]
  obtain ⟨hnone, hsome⟩ := parse_run (a := c₀) (b := K * (c₀ + 1)) (f := K + 2) (mode := mode)
    N y hyB
  cases hd : pairDecode y with
  | none =>
    rw [indicator_eq_decide, cdec_false (by
      cases mode <;> simpa [qLang] using not_mem_indexLang_of_pairDecode hd)]
    exact hnone hd
  | some xb =>
    obtain ⟨x, β⟩ := xb
    have hy := eq_pairEncode_of_pairDecode y x β hd
    have hylen : y.length = 2 * x.length + 2 + β.length := by rw [hy, length_pairEncode]
    set E := K * (c₀ + 1) * ell x.length + (K + 2) with hE
    have hnE : nV K c₀ x.length = 2 ^ E := rfl
    have hmono : 2 ^ E ≤ nV K c₀ y.length := by rw [← hnE]; exact nV_mono K c₀ (by omega)
    have hsq : (2 ^ E) ^ 2 ≤ nV K c₀ y.length ^ 2 := Nat.pow_le_pow_left hmono 2
    have h4 : 4 ≤ 2 ^ E := by rw [← hnE]; exact four_le_nV K c₀ _
    have hsq2 : 2 ^ E ≤ (2 ^ E) ^ 2 := by nlinarith
    have r1 := hsome x β hy
    have r2 := setup_run (a := c₀) (b := K * (c₀ + 1)) (f := K + 2) (mode := mode) (B := B) N y
      y.length x.length (c₀_le N c₀) (by omega) (by rw [← hE]; omega)
    refine (r1.trans r2).halt ?_
    rcases check_decode_run (a := c₀) (b := K * (c₀ + 1)) (f := K + 2) (mode := mode) (B := B)
      N x β y hy (setSt y.length (2 * x.length + 2) x.length (c₀ * ell x.length) E)
      (by simp only [setSt, St.Bd]; have := Nat.mul_le_mul_left c₀ (ell_mono (Nat.le_refl x.length))
          have h5 : c₀ * ell x.length ≤ E := by
            have := Nat.mul_le_mul_right (ell x.length) (c₀_le N c₀); simp only [hE]; nlinarith
          have h6 : E < 2 ^ E := Nat.lt_two_pow_self
          omega)
      rfl rfl rfl rfl rfl (by simp only [setSt]; omega)
      (by simp only [setSt]; omega) with
      ⟨hw, hcan, q', k', hq', hk', r3⟩ | ⟨hbad, r3⟩
    · -- a query `⟨x, bits i⟩` in range: the walk
      have hβ := canon_eq_bits β hcan
      set i := LogProg.bitsVal β with hi
      have hiB : i ≤ 2 * (4 * (2 ^ E) ^ 2) := by
        have := Codec.bitsVal_le_of_width β _ (by simp only [setSt]; omega) hw 0
        simpa [setSt] using this
      refine r3.halt ?_
      have r4 := walk_halt (a := c₀) (b := K * (c₀ + 1)) (f := K + 2) (mode := mode) (B := B)
        N x β ⟨2 * x.length + 2, 2 * x.length + 2, x.length, 0, 0, c₀ * ell x.length, E,
          2 * 2 ^ E, 2 * (2 ^ E) ^ 2, k', q', i, 0, 0, 0⟩
        (by
          simp only [St.Bd]
          have h5 : c₀ * ell x.length ≤ E := by
            have := Nat.mul_le_mul_right (ell x.length) (c₀_le N c₀); simp only [hE]; nlinarith
          have h6 : E < 2 ^ E := Nat.lt_two_pow_self
          omega)
        rfl rfl rfl rfl rfl rfl rfl
      rw [← hy] at r4
      have e1 : wAns N x mode (c₀ * ell x.length) E i =
          MultiTapeTM.indicator (qLang N c₀ mode : Set (List Bool)) y := by
        rw [wAns_eq, hy, ← hβ]
      rw [e1] at r4
      simpa [setSt] using r4
    · -- no query, or an index beyond the output
      have hfalse : MultiTapeTM.indicator (qLang N c₀ mode : Set (List Bool)) y = false := by
        rw [indicator_eq_decide]
        apply cdec_false
        intro hmem
        obtain ⟨x', i', he, hp⟩ : ∃ x' i', y = pairEncode x' (Nat.bits i') ∧
            (if mode then i' < (red N c₀ x').length
              else (red N c₀ x').getD i' false = true) := by
          cases mode <;> simpa [qLang] using hmem
        obtain ⟨rfl, hβ⟩ := Codec.pairEncode_inj (hy.symm.trans he)
        subst hβ
        have hwide : 4 * (2 ^ E) ^ 2 < i' := by
          by_contra hc
          exact hbad ⟨by simpa [setSt] using length_bits_mono (not_lt.mp hc), canon_bits i'⟩
        have hlen : (red N c₀ x).length < i' := by
          rw [length_red, hnE]; nlinarith
        cases mode with
        | true => simp only [if_true] at hp; omega
        | false =>
          simp only [Bool.false_eq_true, if_false] at hp
          rw [List.getD_eq_default _ _ (by omega)] at hp
          cases hp
      rw [hfalse]
      exact r3

/-- **The register bound is polynomial**: `qBnd y ≤ (8 D² + 9) (|y| + 1) ^ (2e + 1)`, with
`D = 2 ^ (K + 2) · 2 ^ e` and `e = K (c₀ + 1)` (`nV_le`). -/
lemma qBnd_le (y : List Bool) :
    qBnd N c₀ y ≤ (8 * (2 ^ (codeK N + 2) * 2 ^ (codeK N * (c₀ + 1))) ^ 2 + 9) *
      (y.length + 1) ^ (2 * (codeK N * (c₀ + 1)) + 1) := by
  set e := codeK N * (c₀ + 1)
  set D := 2 ^ (codeK N + 2) * 2 ^ e
  have hn := nV_le (codeK N) c₀ y.length
  set q := (y.length + 1) ^ e
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by omega)
  have e1 : (y.length + 1) ^ (2 * e + 1) = q ^ 2 * (y.length + 1) := by
    rw [pow_succ, pow_mul']
  rw [e1]
  have h1 : nV (codeK N) c₀ y.length ^ 2 ≤ (D * q) ^ 2 := Nat.pow_le_pow_left hn 2
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : y.length + 1 ≤ q ^ 2 * (y.length + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : (D * q) ^ 2 ≤ D ^ 2 * (q ^ 2 * (y.length + 1)) := by
    rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
  unfold qBnd
  nlinarith

/-- **The reduction is implicitly logspace computable** [AB09, Theorem 4.18: the reduction
`x ↦ ⟨G_{N,x}, C_start, C_accept⟩` is implicitly logspace computable].

**Proof sketch.** The output length is polynomial (`length_red_le`). Each query language is
decided by the query machine in the corresponding mode (`query_halts`), which calls logspace
deciders (`As_mem`) and keeps its registers below a polynomial (`qBnd_le`);
`Complexity.LogProg.arm_decides_poly` concludes. -/
theorem implicitlyLogspaceComputable_red : ImplicitlyLogspaceComputable (red N c₀) := by
  have hmode : ∀ mode, qLang N c₀ mode ∈ LOGSPACE := by
    intro mode
    refine arm_decides_poly (A c₀ (codeK N * (c₀ + 1)) (codeK N + 2) mode) .lenQ (As N)
      (As_mem N) _ _ fun y => (query_halts N c₀ mode y).mono fun a h =>
        ⟨h.1, fun r => (h.2 r).trans (qBnd_le N c₀ y)⟩
  exact ⟨length_red_le N c₀, by simpa [qLang] using hmode false, by simpa [qLang] using hmode true⟩

end Complexity.PathHard

namespace Complexity

open Turing

/-- **`PATH` is `NL`-hard, for the raw encoding** [AB09, Theorem 4.18]: every language in
`NL` logspace-reduces to `pathRawLang`.

**Proof sketch.** For `L` decided by `N` in space `c₀ · logSpace`, the configuration-graph
reduction `PathHard.red N c₀` is correct (`PathHard.red_mem_iff`) and implicitly logspace
computable (`PathHard.implicitlyLogspaceComputable_red`). -/
theorem pathRawLang_NLHard {L : Language Bool} (hL : L ∈ NL) : L ≤ₗ pathRawLang := by
  obtain ⟨c₀, N, hN⟩ := hL
  exact ⟨PathHard.red N c₀, PathHard.implicitlyLogspaceComputable_red N c₀,
    PathHard.red_mem_iff N hN⟩

end Complexity
