/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.BPLInPCount
import TCSlib.Complexity.Randomized.BPLInPWords
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `BPL ⊆ P`

[AB09, Exercise 7.9]: every language of `BPL` is decided in polynomial time. A log-space PTM
`N` has polynomially many configuration codes, and the table `Randomized.BPLInP.dpVal`
(`TCSlib.Complexity.Randomized.BPLInPCount`) computes `2^V · Pr[N(x) = 1]` exactly, in `V`
rounds over `V` codes, each entry a sum of entries of the previous round selected by the
step tests of the code languages. This file writes the table as a polynomial-time word
function — the rounds by `Complexity.BinArith.polyTimeComputable_iterate`, a round by the map
and zip loops of `Complexity.BinArith`, the step and accepting-code tests by `L ⊆ P` — and
accepts iff `2^V < 2 · dpVal`.

## Main definitions

* `Randomized.BPLInP.dpStep`, `Randomized.BPLInP.dpInit`, `Randomized.BPLInP.dpRun` — the
  rounds of the table on the state `⟨⟨x, ⟨bits s, codes⟩⟩, table⟩`.
* `Randomized.BPLInP.bplTest` — the polynomial-time test.

## Main results

* `Randomized.BPLInP.polyTimeComputable_bplTest` — the test is polynomial-time.
* `Randomized.BPLInP.bplTest_eq` — it compares `2^V` with `2 · dpVal` at the initial code.
* `Randomized.BPL_subset_P` — `BPL ⊆ P`. [AB09, Exercise 7.9]

## Divergences

* The window radius is `s = c · (|bits |x|| + 1)` rather than the space bound `c · logSpace |x|`
  itself (it is at least that, and computable in binary by a length count), and the table has
  `V = 8^e (|x| + 1)^e` rows, `e = codeK N · (c + 1)`, a polynomial bound on the number of codes
  `2 ^ (codeK N · (s + logSpace |x| + 1))`; rows beyond the codes stay unused.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.BPLInP

open Complexity Complexity.Codec Complexity.BinArith Turing
open Complexity.LogProg (bitsVal bitsVal_bits)

variable (N : FinNDTM Bool) (c B e : ℕ)

/-! ### The word functions -/

/-- The context `⟨x, ⟨bits s, codes⟩⟩` of the dynamic program. -/
def ctxW (x : List Bool) : List Bool := pairEncode x (pairEncode (radius c x) (codesW B e x))

/-- The coin-`b` step test on `⟨⟨x, ⟨r, a⟩⟩, ⟨a', _⟩⟩`: is `⟨x, ⟨a, ⟨a', r⟩⟩⟩` a step pair of
`fixCoin N b`? -/
noncomputable def stepTest (b : Bool) (z : List Bool) : Bool :=
  MultiTapeTM.indicator (stepLang (fixCoin N b) : Set (List Bool))
    (pairEncode (pairFstD (pairFstD z)) (pairEncode (pairSndD (pairSndD (pairFstD z)))
      (pairEncode (pairFstD (pairSndD z)) (pairFstD (pairSndD (pairFstD z))))))

/-- A summand of a table entry on `⟨⟨x, ⟨r, a⟩⟩, ⟨a', v⟩⟩`: `v` once per coin stepping `a` to
`a'`. -/
noncomputable def entryW (z : List Bool) : List Bool :=
  add (pairEncode (if stepTest N false z then pairSndD (pairSndD z) else [])
    (if stepTest N true z then pairSndD (pairSndD z) else []))

/-- The new table entry on `⟨⟨Q, table⟩, a⟩`, `Q = ⟨x, ⟨r, codes⟩⟩`: the sum of the summands
over the codes. -/
noncomputable def rowW (y : List Bool) : List Bool :=
  sumW (zipWithW (entryW N) (pairEncode
    (pairEncode (pairFstD (pairFstD (pairFstD y)))
      (pairEncode (pairFstD (pairSndD (pairFstD (pairFstD y)))) (pairSndD y)))
    (pairEncode (pairSndD (pairSndD (pairFstD (pairFstD y)))) (pairSndD (pairFstD y)))))

/-- One round of the table on `⟨Q, table⟩`. -/
noncomputable def dpStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S) (mapW (rowW N) (pairEncode S (pairSndD (pairSndD (pairFstD S)))))

/-- The initial entry on `⟨Q, a⟩`: `1` iff `a` is an accepting code. -/
noncomputable def initEntry (y : List Bool) : List Bool :=
  if MultiTapeTM.indicator (acceptLang N : Set (List Bool)) (pairEncode (pairFstD (pairFstD y))
    (pairEncode (pairSndD y) (pairFstD (pairSndD (pairFstD y))))) then [true] else []

/-- The initial state `⟨Q, table₀⟩`. -/
noncomputable def dpInit (x : List Bool) : List Bool :=
  pairEncode (ctxW c B e x) (mapW (initEntry N) (pairEncode (ctxW c B e x) (codesW B e x)))

/-- The state after `V = B (|x| + 1)^e` rounds. -/
noncomputable def dpRun (x : List Bool) : List Bool :=
  (dpStep N)^[B * (x.length + 1) ^ e] (dpInit N c B e x)

/-- The entry on `⟨Q, ⟨a, v⟩⟩` kept by the final read: `v` iff `a` is the initial code. -/
noncomputable def pickW (z : List Bool) : List Bool :=
  if MultiTapeTM.indicator (initLang N : Set (List Bool)) (pairEncode (pairFstD (pairFstD z))
    (pairEncode (pairFstD (pairSndD z)) (pairFstD (pairSndD (pairFstD z))))) then
    pairSndD (pairSndD z) else []

/-- The final table entry at the initial code. -/
noncomputable def accW (x : List Bool) : List Bool :=
  sumW (zipWithW (pickW N) (pairEncode (pairFstD (dpRun N c B e x))
    (pairEncode (pairSndD (pairSndD (pairFstD (dpRun N c B e x)))) (pairSndD (dpRun N c B e x)))))

/-- **The test**: is `2^V < 2 · (the final entry at the initial code)`? -/
noncomputable def bplTest (x : List Bool) : Bool :=
  BinArith.lt (pairEncode (pow2W B e x) (false :: accW N c B e x))

/-! ### Polynomial time -/

/-- Composition in applied form (`Complexity.BinArith.polyTimeComputable_app`). -/
local notation "ptA" => Complexity.BinArith.polyTimeComputable_app

/-- A one-bit test of a function (`Complexity.BinArith.polyTimeComputable_test_app`). -/
local notation "ptT" => Complexity.BinArith.polyTimeComputable_test_app

/-- The step test is polynomial-time. -/
theorem polyTimeComputable_stepTest (b : Bool) :
    PolyTimeComputable (fun z => [stepTest N b z]) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hA := polyTimeComputable_indicator_of_LOGSPACE (stepLang_mem (N := fixCoin N b))
  unfold stepTest
  exact ptT hA
    ((ptA h1 h1).pairEncode ((ptA h2 (ptA h2 h1)).pairEncode
      ((ptA h1 h2).pairEncode (ptA h1 (ptA h2 h1)))))

/-- The round is polynomial-time. -/
theorem polyTimeComputable_dpStep : PolyTimeComputable (dpStep N) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hv : PolyTimeComputable (fun z : List Bool => pairSndD (pairSndD z)) := ptA h2 h2
  have hentry : PolyTimeComputable (entryW N) := by
    unfold entryW; exact ptA polyTimeComputable_add
      ((polyTimeComputable_ite (polyTimeComputable_stepTest N false) hv
        (polyTimeComputable_const [])).pairEncode
      (polyTimeComputable_ite (polyTimeComputable_stepTest N true) hv
        (polyTimeComputable_const [])))
  have hrow : PolyTimeComputable (rowW N) := by
    unfold rowW; exact ptA polyTimeComputable_sumW (ptA (polyTimeComputable_zipWithW hentry)
      (((ptA h1 (ptA h1 h1)).pairEncode ((ptA h1 (ptA h2 (ptA h1 h1))).pairEncode
        h2)).pairEncode ((ptA h2 (ptA h2 (ptA h1 h1))).pairEncode (ptA h2 h1))))
  unfold dpStep
  exact h1.pairEncode (ptA (polyTimeComputable_mapW hrow)
    (polyTimeComputable_id.pairEncode (ptA h2 (ptA h2 h1))))

/-- The initial state is polynomial-time. -/
theorem polyTimeComputable_dpInit : PolyTimeComputable (dpInit N c B e) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hctx : PolyTimeComputable (ctxW c B e) := by
    unfold ctxW; exact
    polyTimeComputable_id.pairEncode
      ((polyTimeComputable_radius c).pairEncode (polyTimeComputable_codesW B e))
  have hi : PolyTimeComputable (initEntry N) := by
    have hA := polyTimeComputable_indicator_of_LOGSPACE (acceptLang_mem (N := N))
    unfold initEntry; exact polyTimeComputable_ite (ptT hA
      ((ptA h1 h1).pairEncode (h2.pairEncode (ptA h1 (ptA h2 h1)))))
      (polyTimeComputable_const [true]) (polyTimeComputable_const [])
  unfold dpInit
  exact hctx.pairEncode (ptA (polyTimeComputable_mapW hi)
    (hctx.pairEncode (polyTimeComputable_codesW B e)))

/-- The final entry is polynomial-time, given the rounds. -/
theorem polyTimeComputable_bplTest_of_run (hrun : PolyTimeComputable (dpRun N c B e)) :
    PolyTimeComputable (fun x => [bplTest N c B e x]) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hpick : PolyTimeComputable (pickW N) := by
    have hA := polyTimeComputable_indicator_of_LOGSPACE (initLang_mem (N := N))
    unfold pickW; exact polyTimeComputable_ite (ptT hA
      ((ptA h1 h1).pairEncode ((ptA h1 h2).pairEncode (ptA h1 (ptA h2 h1)))))
      (ptA h2 h2) (polyTimeComputable_const [])
  have hacc : PolyTimeComputable (accW N c B e) := by
    unfold accW; exact ptA polyTimeComputable_sumW (ptA (polyTimeComputable_zipWithW hpick)
      ((ptA h1 hrun).pairEncode ((ptA h2 (ptA h2 (ptA h1 hrun))).pairEncode
        (ptA h2 hrun))))
  unfold bplTest
  exact ptT polyTimeComputable_lt
    ((polyTimeComputable_pow2W B e).pairEncode (ptA (polyTimeComputable_prepend [false]) hacc))

/-! ### What the word functions compute -/

section Semantics

variable {N} (x : List Bool)

/-- A list sum over `range V` is the `Finset` sum. -/
theorem sum_map_range (f : ℕ → ℕ) (V : ℕ) :
    ((List.range V).map f).sum = ∑ i ∈ Finset.range V, f i := by
  induction V with
  | zero => rfl
  | succ V ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- Mapping into binary words factors through the map of values. -/
theorem map_bits (f : ℕ → ℕ) (l : List ℕ) :
    l.map (fun a => Nat.bits (f a)) = (l.map f).map Nat.bits := by simp

/-- The context with radius `s` and `V` codes. -/
def ctxOf (s V : ℕ) : List Bool :=
  pairEncode x (pairEncode (Nat.bits s) (encWords ((List.range V).map Nat.bits)))

variable (N) in
/-- The table after `t` rounds, encoded. -/
noncomputable def vecW (s V t : ℕ) : List Bool :=
  encWords ((List.range V).map fun a => Nat.bits (dpVal N x s V t a))

/-- `ctxW` is the context of radius `c (|bits |x|| + 1)` and `B (|x| + 1)^e` codes. -/
theorem ctxW_eq : ctxW c B e x =
    ctxOf x (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e) := by
  rw [ctxW, codesW_eq, radius, ctxOf]

open Classical in
/-- A summand of an entry. -/
theorem entryW_eq (s a a' v : ℕ) :
    entryW N (pairEncode (pairEncode x (pairEncode (Nat.bits s) (Nat.bits a)))
      (pairEncode (Nat.bits a') (Nat.bits v))) =
      Nat.bits ((if StepRel (fixCoin N false) x s a a' then v else 0) +
        (if StepRel (fixCoin N true) x s a a' then v else 0)) := by
  simp only [entryW, stepTest, pairFstD_pairEncode, pairSndD_pairEncode, MultiTapeTM.indicator,
    StepRel]
  split_ifs <;> simp_all [add, bitsVal_bits, LogProg.bitsVal]

/-- The initial state is the context and the table after `0` rounds. -/
theorem dpInit_eq : dpInit N c B e x = pairEncode (ctxW c B e x)
    (vecW N x (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e) 0) := by
  classical
  rw [dpInit, codesW_eq, mapW_pairEncode, decWords_encWords, List.map_map, vecW]
  refine congrArg (pairEncode _) (congrArg encWords ?_)
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp, initEntry, pairFstD_pairEncode, pairSndD_pairEncode, ctxW, radius,
    MultiTapeTM.indicator, dpVal]
  split_ifs <;> simp_all [Nat.one_bits]

/-- **A round computes the next table.** -/
theorem dpStep_eq (s V t : ℕ) :
    dpStep N (pairEncode (ctxOf x s V) (vecW N x s V t)) =
      pairEncode (ctxOf x s V) (vecW N x s V (t + 1)) := by
  classical
  simp only [dpStep, pairFstD_pairEncode, pairSndD_pairEncode, ctxOf]
  rw [mapW_pairEncode, decWords_encWords, List.map_map, vecW]
  refine congrArg (pairEncode _) (congrArg encWords ?_)
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp, rowW, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [zipWithW_pairEncode, decWords_encWords, decWords_encWords, List.zipWith_map,
    List.zipWith_self]
  simp only [entryW_eq]
  rw [map_bits, sumW_encWords, sum_map_range, dpVal]

/-- The rounds of the table. -/
theorem iterate_dpStep (s V t : ℕ) :
    (dpStep N)^[t] (pairEncode (ctxOf x s V) (vecW N x s V 0)) =
      pairEncode (ctxOf x s V) (vecW N x s V t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, dpStep_eq]

/-- The state after `i` rounds. -/
theorem iterate_dpInit (i : ℕ) : (dpStep N)^[i] (dpInit N c B e x) = pairEncode (ctxW c B e x)
    (vecW N x (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e) i) := by
  rw [dpInit_eq, ctxW_eq, iterate_dpStep]

/-- **The test compares `2^V` with twice the table at the initial code.**

**Proof sketch.** After `V` rounds the state holds the table after `V` rounds
(`iterate_dpInit`); the final read keeps the entry whose code passes the initial-code test,
which is exactly the code of the initial configuration (`mem_initLang`, below `V` by
`cfgCode_lt`), and sums (`sumW_encWords`); `pow2W` has value `2^V` and prepending `0` doubles. -/
theorem bplTest_eq (hV : 2 ^ (codeK N * (c * ((Nat.bits x.length).length + 1) +
      logSpace x.length + 1)) ≤ B * (x.length + 1) ^ e) :
    bplTest N c B e x = decide (2 ^ (B * (x.length + 1) ^ e) < 2 * dpVal N x
      (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e)
      (B * (x.length + 1) ^ e) (cfgCode (c * ((Nat.bits x.length).length + 1))
        (N.tm.initCfg x))) := by
  classical
  set s := c * ((Nat.bits x.length).length + 1) with hs_def
  set V := B * (x.length + 1) ^ e with hV_def
  have hacc : accW N c B e x = Nat.bits (dpVal N x s V V (cfgCode s (N.tm.initCfg x))) := by
    rw [accW, dpRun, iterate_dpInit, ctxW_eq, ← hs_def, ← hV_def]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, ctxOf, vecW]
    rw [zipWithW_pairEncode, decWords_encWords, decWords_encWords, List.zipWith_map,
      List.zipWith_self]
    have hpick : ∀ a, pickW N (pairEncode (pairEncode x (pairEncode (Nat.bits s)
        (encWords ((List.range V).map Nat.bits)))) (pairEncode (Nat.bits a)
          (Nat.bits (dpVal N x s V V a)))) = Nat.bits
          (if cfgCode s (N.tm.initCfg x) = a then dpVal N x s V V a else 0) := by
      intro a
      have hm := mem_initLang N x a s
      simp only [pickW, pairFstD_pairEncode, pairSndD_pairEncode, MultiTapeTM.indicator]
      by_cases h : cfgCode s (N.tm.initCfg x) = a
      · simp only [hm, h, ↓reduceIte]
      · simp only [hm, h, ↓reduceIte, Bool.false_eq_true, Nat.zero_bits]
    simp only [hpick]
    rw [map_bits, sumW_encWords, sum_map_range, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.mpr ((cfgCode_lt s _).trans_le hV))]
  rw [bplTest, BinArith.lt, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_pow2W, hacc]
  simp [LogProg.bitsVal, bitsVal_bits, s, V]

/-! ### Length bounds -/

/-- The encoded table after `t` rounds has length at most `V (2 (2Vt + 1) + 2)`. -/
theorem length_vecW_le (s V t : ℕ) :
    (vecW N x s V t).length ≤ V * (2 * (2 * V * t + 1) + 2) := by
  have := length_encWords_le ((List.range V).map fun a => Nat.bits (dpVal N x s V t a))
    (2 * V * t + 1) (by
      intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
      apply LogProg.length_bits_le
      calc dpVal N x s V t a ≤ (2 * V) ^ t := dpVal_le N x s V t a
        _ ≤ (2 ^ (2 * V)) ^ t := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le t
        _ = 2 ^ (2 * V * t) := by rw [← pow_mul]
        _ < 2 ^ (2 * V * t + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega))
  simpa [vecW] using this

/-- The context has length at most `2|x| + 2s + 4 + V (2V + 2)`. -/
theorem length_ctxOf_le (s V : ℕ) :
    (ctxOf x s V).length ≤ 2 * x.length + 2 * s + 4 + V * (2 * V + 2) := by
  have h1 := Turing.length_bits_le_self s
  have h2 := length_encWords_range_le V
  simp only [ctxOf, length_pairEncode]
  omega

end Semantics

/-- **The rounds run in polynomial time.**

**Proof sketch.** `Complexity.BinArith.polyTimeComputable_iterate` of the round from the
initial state. After `i ≤ V` rounds the state is the context and the table after `i` rounds
(`iterate_dpInit`); its entries are below `(2V)^i` (`dpVal_le`), so the state has length
`O((|x| + 1)(V + 1)^3)`, a polynomial since `V = B (|x| + 1)^e`. -/
theorem polyTimeComputable_dpRun : PolyTimeComputable (dpRun N c B e) := by
  refine polyTimeComputable_iterate (polyTimeComputable_dpStep N)
    (polyTimeComputable_dpInit N c B e) B e ((22 + 4 * c) * (B + 1) ^ 3) (3 * e + 1)
    fun x i hi => ?_
  rw [iterate_dpInit, ctxW_eq, length_pairEncode]
  set n := x.length
  set V := B * (n + 1) ^ e
  set s := c * ((Nat.bits n).length + 1)
  have h1 := length_ctxOf_le x s V
  have h2 := length_vecW_le (N := N) x s V i
  have hs : s ≤ c * (n + 1) :=
    Nat.mul_le_mul_left _ (by have := Turing.length_bits_le_self n; omega)
  set P := n + 1
  set W := V + 1
  have hP1 : 1 ≤ P := by omega
  have hW1 : 1 ≤ W := by omega
  have hW3 : 1 ≤ W ^ 3 := Nat.one_le_pow _ _ hW1
  have hPW : P ≤ P * W ^ 3 := Nat.le_mul_of_pos_right _ hW3
  have hWW : W ^ 3 ≤ P * W ^ 3 := Nat.le_mul_of_pos_left _ hP1
  have hW2 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hcP : c * P ≤ c * (P * W ^ 3) := Nat.mul_le_mul_left _ hPW
  have hvi : V * (2 * (2 * V * i + 1) + 2) ≤ 4 * W ^ 3 := by
    have : 2 * V * i ≤ 2 * V * V := Nat.mul_le_mul_left _ hi
    calc V * (2 * (2 * V * i + 1) + 2) ≤ V * (2 * (2 * V * V + 1) + 2) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 4 * W ^ 3 := by simp only [W]; ring_nf; nlinarith
  have hcod : V * (2 * V + 2) ≤ 2 * W ^ 2 := by simp only [W]; ring_nf; nlinarith
  have htot : 2 * (2 * n + 2 * s + 4 + V * (2 * V + 2)) + 2 + V * (2 * (2 * V * i + 1) + 2) ≤
      (22 + 4 * c) * (P * W ^ 3) := by
    have : n ≤ P := by omega
    nlinarith
  have hWB : W ≤ (B + 1) * P ^ e := by
    have : 1 ≤ P ^ e := Nat.one_le_pow _ _ hP1
    have hPe : P ^ e = (n + 1) ^ e := rfl
    simp only [W, V]; rw [hPe, add_mul, one_mul]; omega
  have hfin : P * W ^ 3 ≤ (B + 1) ^ 3 * P ^ (3 * e + 1) := by
    calc P * W ^ 3 ≤ P * ((B + 1) * P ^ e) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWB 3)
      _ = (B + 1) ^ 3 * P ^ (3 * e + 1) := by ring
  calc 2 * (ctxOf x s V).length + 2 + (vecW N x s V i).length
      ≤ (22 + 4 * c) * (P * W ^ 3) := by omega
    _ ≤ (22 + 4 * c) * ((B + 1) ^ 3 * P ^ (3 * e + 1)) := Nat.mul_le_mul_left _ hfin
    _ = (22 + 4 * c) * (B + 1) ^ 3 * (x.length + 1) ^ (3 * e + 1) := by ring

/-- **The test is polynomial-time.** -/
theorem polyTimeComputable_bplTest : PolyTimeComputable (fun x => [bplTest N c B e x]) :=
  polyTimeComputable_bplTest_of_run N c B e (polyTimeComputable_dpRun N c B e)

/-- The number of codes is polynomial: with `e = codeK N · (c + 1)`, the codes at radius
`c (|bits n| + 1)` are below `8^e (n + 1)^e`.

**Proof sketch.** With `m = |bits n|`: `logSpace n ≤ m + 1` and `2^m ≤ 2(n + 1)`
(`Nat.lt_size`), so the exponent is at most `e (m + 2)` and
`2^{e(m+2)} = (4 · 2^m)^e ≤ (8(n + 1))^e`. -/
theorem two_pow_codes_le (n : ℕ) :
    2 ^ (codeK N * (c * ((Nat.bits n).length + 1) + logSpace n + 1)) ≤
      8 ^ (codeK N * (c + 1)) * (n + 1) ^ (codeK N * (c + 1)) := by
  set m := (Nat.bits n).length
  have hlog : logSpace n ≤ m + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [logSpace]
    · have : Nat.log 2 n < m := by
        rw [show m = n.size from Nat.size_eq_bits_len n]
        exact Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
      simp only [logSpace]; omega
  have hpow : 2 ^ m ≤ 2 * (n + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [m]
    · have hm : m = n.size := Nat.size_eq_bits_len n
      have hpos : 0 < m := by rw [hm]; exact Nat.size_pos.mpr hn
      have : 2 ^ (m - 1) ≤ n := by rw [hm] at hpos ⊢; exact Nat.lt_size.mp (by omega)
      calc 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
        _ ≤ 2 * (n + 1) := by omega
  set e := codeK N * (c + 1)
  calc 2 ^ (codeK N * (c * (m + 1) + logSpace n + 1)) ≤ 2 ^ (e * (m + 2)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        simp only [e, mul_assoc]
        refine Nat.mul_le_mul_left _ ?_
        nlinarith
    _ = (4 * 2 ^ m) ^ e := by rw [mul_comm, pow_mul]; ring
    _ ≤ (8 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
    _ = 8 ^ e * (n + 1) ^ e := mul_pow _ _ _

end Randomized.BPLInP

namespace Randomized

open Complexity Complexity.Codec Turing BPLInP

/-- **`BPL ⊆ P`.** [AB09, Exercise 7.9]

**Proof sketch.** Let `N` decide `L` with bounded error in space `c · logSpace`. At radius
`s = c (|bits |x|| + 1)` its configurations have codes below `V = 8^e (|x| + 1)^e`
(`two_pow_codes_le`), so it halts within `V` steps (`haltsWithin_of_codes`) and the table after
`V` rounds is `2^V · Pr[N(x) = 1]` at the initial code (`dpVal_init`). The test
`BPLInP.bplTest` computes exactly `2^V < 2 · dpVal` (`bplTest_eq`) in polynomial time
(`polyTimeComputable_bplTest`), and this holds iff `Pr[N(x) = 1] > 1/2`, i.e. iff `x ∈ L`: a
member is accepted with probability `≥ 2/3`, a non-member rejected with probability
`≥ 2/3`, so accepted with probability `≤ 1/3`. -/
theorem BPL_subset_P : BPL ⊆ P := by
  rintro L ⟨c, N, hUS, hdec⟩
  set e := codeK N * (c + 1)
  have key : ∀ x, bplTest N c (8 ^ e) e x = true ↔ x ∈ L := by
    intro x
    obtain ⟨T, hT, hp⟩ := hdec x
    set s := c * ((Nat.bits x.length).length + 1)
    set V := 8 ^ e * (x.length + 1) ^ e
    have hs : c * logSpace x.length ≤ s := by
      refine Nat.mul_le_mul_left _ ?_
      rcases Nat.eq_zero_or_pos x.length with h0 | hn
      · simp [h0, logSpace]
      · have : Nat.log 2 x.length < (Nat.bits x.length).length := by
          rw [Nat.size_eq_bits_len]
          exact Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
        simp only [logSpace]; omega
    have hV := two_pow_codes_le N c x.length
    have hHV : N.tm.HaltsWithin x V := haltsWithin_of_codes hUS hs hV hT
    have hdp := dpVal_init hUS hs hV hT
    have heq : N.outputProb x V [true] = N.outputProb x T [true] := by
      rw [← FinNDTM.outputProb_eq_of_haltsWithin hHV (le_max_left V T),
        FinNDTM.outputProb_eq_of_haltsWithin hT (le_max_right V T)]
    rw [heq] at hdp
    rw [bplTest_eq c (8 ^ e) e x hV, decide_eq_true_iff]
    set d := dpVal N x s V V (cfgCode s (N.tm.initCfg x))
    have h2V : (0 : ℚ) < 2 ^ V := by positivity
    have hiff : 2 ^ V < 2 * d ↔ (2 : ℚ) ^ V < 2 * ((2 : ℚ) ^ V * N.outputProb x T [true]) := by
      rw [← hdp]; exact_mod_cast Iff.rfl
    rw [hiff]
    classical
    by_cases hx : x ∈ L
    · simp only [MultiTapeTM.indicator, hx, if_true] at hp
      simp only [hx, iff_true]
      nlinarith
    · simp only [MultiTapeTM.indicator, hx, if_false] at hp
      simp only [hx, iff_false, not_lt]
      have hsum : N.outputProb x T [true] + N.outputProb x T [false] ≤ 1 := by
        unfold FinNDTM.outputProb
        rw [← randProb_or_disjoint _ _ fun r h => by
          have := h.1.symm.trans h.2
          simp at this]
        exact randProb_le_one
      nlinarith
  have hL : L = {x | bplTest N c (8 ^ e) e x = true} := Set.ext fun x => (key x).symm
  rw [hL]
  exact mem_P_of_test (polyTimeComputable_bplTest N c (8 ^ e) e)

end Randomized
