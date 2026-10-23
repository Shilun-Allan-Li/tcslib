/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.UPathSearch
import TCSlib.Complexity.Randomized.UPathWalk
import TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `UPATH ∈ RL`

[AB09, Theorem 7.19] ([AKL+79]): undirected `s`-`t` connectivity is in randomized
logarithmic space. The machine `Complexity.LogProg.upA` checks the input deterministically,
then takes a random walk of length `100 n⁴` from `s` and accepts iff it visits `t`. Composed
from the start (`Complexity.LogProg.ups_start`), its acceptance probability is `0` on
strings that are not symmetric `UPATH` instances, and otherwise the hitting probability of
`t` from `s` in the padded graph (`Complexity.upGraph`): at least `3/4` if `t` is reachable
(`Randomized.RegularMultigraph.three_quarters_le_hitProb`), `0` if not. Its registers stay
below `200 (|x| + 1)⁴`, so `Complexity.LogProg.narm_mem_RL` places `UPATH` in `RL`.

## Main definitions

* `Complexity.LogProg.UReg.zero` — the initial register file.

## Main results

* `Complexity.LogProg.ups_start` — the semantics of the machine.
* `Complexity.UPATH_mem_RL` — [AB09, Theorem 7.19].

## Divergences

* The walk is the walk on the padded graph of [AB09, Exercise 7.11(e)]: a step reads
  `size n` coins as a slot `i < 2^{size n}` and moves to `i` if `i < n` and `{v, i}` is an
  edge, staying put otherwise — the book's "choose a random neighbor" up to self-loops, as
  recorded in `TCSlib.Complexity.Randomized.RandomWalkPad`.
* The endpoints are found deterministically (not guessed), and the matrix is checked to be
  symmetric, so that strings outside `UPATH` are rejected on every branch, as `RL` requires.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7, Theorem 7.19.)
* [AKL+79] R. Aleliunas, R. M. Karp, R. J. Lipton, L. Lovász, C. Rackoff, *Random walks,
  universal traversal sequences, and the complexity of maze problems*, FOCS 1979.
-/

namespace Complexity

open Turing

namespace LogProg

open ULabel UPathTac Randomized

/-- The register file at the start: all registers `0`. -/
def UReg.zero : UReg := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The semantics of the machine**: with registers bounded by `200 (|x| + 1)⁴`, the
machine accepts with probability `q` provided `q = 0` when `x` has no symmetric instance
layout, and `q` is the `100 n⁴`-step hitting probability of `t` from `s` when `x` has the
layout of `n`, `s`, `t` with a symmetric matrix.

**Proof sketch.** Compose the phases from the start: `ups_unary`, `ups_mat`, the copy saving
the source position, `ups_yrow`, `ups_ssearch`, the copy saving the target position,
`ups_tsearch`, `ups_len` and `ups_walk`. Each failing check rejects, and then no layout
exists, since the layout determines `n`, `s`, `t` (`unaryRest_unique`, `dblAt_unique`,
`Complexity.LogProg.bits_injective`); at the walk the checks give the layout of `n`, `s`,
`t`. The register bounds come from the separators lying inside the input. -/
theorem ups_start (x : List Bool) (q : ℚ)
    (hfail : (¬ ∃ n s t, UShape x n s t ∧ SymRest x n) → q = 0)
    (hwalk : ∀ n s t (h : UShape x n s t) (hsym : SymRest x n),
      q = (upGraph x hsym).hitProb ⟨t, h.2.2.2.2.1⟩ (100 * n ^ 4) ⟨s, h.2.2.1⟩) :
    UPS x (200 * (x.length + 1) ^ 4) u0 UReg.zero q := by
  set B := 200 * (x.length + 1) ^ 4 with hB
  have hx1 : x.length + 1 ≤ (x.length + 1) ^ 4 := by
    calc x.length + 1 = (x.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (x.length + 1) ^ 4 := Nat.pow_le_pow_right (Nat.succ_pos _) (by norm_num)
  have hxB : 2 * x.length + 2 ≤ B := by omega
  have hx4 : ∀ n, n ≤ x.length → 100 * n ^ 4 + 10 * n ≤ B := by
    intro n hn
    have : n ^ 4 ≤ (x.length + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  refine ups_unary q _ _ rfl (by simp only [UReg.zero, UReg.Le]; omega) hxB rfl
    (by simp [UReg.zero]) (fun n _ hU => ?_)
    (fun hne => hfail fun ⟨n, s, t, hS, _⟩ => hne ⟨n, Nat.zero_le _, hS.1⟩)
  simp only [UReg.zero] at hU ⊢
  have hn1 := lt_of_getD_true hU.2.2
  refine ups_mat q _ 0 _ rfl (by uw_le) hxB (by dsimp only; omega) (by simp) (by simp)
    (by simp) (Nat.zero_le _) (fun hMat => ?_) (fun hM => hfail ?_)
  rotate_left
  · rintro ⟨n', s, t, hS, _⟩
    obtain rfl := unaryRest_unique hU hS.1
    exact hM hS.2.1
  simp only at hMat ⊢
  have hm1 := lt_of_getD_true hMat.2.2
  set qs := 2 * n + 2 + 2 * (n * n) + 2 with hqs
  have hnn : 2 * n + 2 + 2 * (n * n) ≤ x.length := by omega
  refine ups_cp .yq q _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
  simp only [cpDst, cpSrc, cpEx]
  uw_regs
  refine UPS.of_eq (σ' := ⟨qs, n, n, 0, 0, 0, 0, 0, 0, qs, 0, 0, 0, 0, 0⟩) (by uw_ext) ?_
  refine ups_yrow q _ _ rfl (by simp only [UReg.Le]; omega) (by dsimp only; omega)
    (Nat.zero_le _) (fun hSym p a b w hp ha hb hw => ?_) (fun hS => hfail ?_)
  rotate_left
  · rintro ⟨n', s, t, hS', hsym⟩
    obtain rfl := unaryRest_unique hU hS'.1
    exact hS fun u' _ hu' w' hw' => hsym u' w' hu' hw'
  have hsym : SymRest x n := fun u w hu hw => hSym u (Nat.zero_le _) hu w hw
  dsimp only at hp ha hb hw ⊢
  refine PSem.clr rfl (UReg.reg (by simp only [UReg.Le]; omega) _ _) ?_
  uw_regs
  refine UPS.of_eq (σ' := ⟨p, n, a, b, 0, 0, 0, 0, 0, qs, 0, 0, w, 0, 0⟩) (by uw_ext) ?_
  refine ups_ssearch q _ _ rfl (by simp only [UReg.Le]; omega) (Nat.zero_le _) rfl
    (by dsimp only; omega) (fun j _ hj hD => ?_) (fun hne => hfail ?_)
  rotate_left
  · rintro ⟨n', s, t, hS', -⟩
    obtain rfl := unaryRest_unique hU hS'.1
    exact hne ⟨s, Nat.zero_le _, hS'.2.2.1, hS'.2.2.2.1⟩
  dsimp only at hj hD ⊢
  have hr := lt_of_getD_true hD.2.2
  have hjb := length_bits_le_self j
  set qt := qs + 2 * (Nat.bits j).length + 2 with hqt
  refine PSem.clr rfl (UReg.reg (by simp only [UReg.Le]; omega) _ _) ?_
  uw_regs
  refine ups_cp .tQ q _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
  simp only [cpDst, cpSrc, cpEx]
  uw_regs
  refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine UPS.of_eq (σ' := ⟨qt, n, a, b, j, 0, 0, 0, 0, qt, 0, 0, w, 0, 0⟩) (by uw_ext) ?_
  refine ups_tsearch q _ _ rfl (by simp only [UReg.Le]; omega) (Nat.zero_le _) rfl
    (by dsimp only; omega) hxB (fun t _ ht hP => ?_) (fun hne => hfail ?_)
  rotate_left
  · rintro ⟨n', s, t, hS', -⟩
    obtain rfl := unaryRest_unique hU hS'.1
    obtain rfl := bits_injective (dblAt_unique hS'.2.2.2.1 hD)
    exact hne ⟨t, Nat.zero_le _, hS'.2.2.2.2.1, hS'.2.2.2.2.2⟩
  dsimp only at ht hP ⊢
  have hS : UShape x n j t := ⟨hU, hMat, hj, hD, ht, hP⟩
  refine ups_len q _ (by simp only [UReg.Le]; omega) rfl rfl rfl (hx4 n (by omega))
    fun a' b' ha' hb' => ?_
  dsimp only
  have hL : n * (10 * n) * (n * (10 * n)) = 100 * n ^ 4 := by ring
  have hLB := hx4 n (by omega)
  have hf : n * (10 * n) ≤ 100 * n ^ 4 + 10 * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · nlinarith [Nat.one_le_pow 2 n h]
  refine (ups_walk hsym ⟨t, ht⟩ hxB hnn _ _ ⟨j, hj⟩ rfl
    (by simp only [UReg.Le]; omega) rfl rfl rfl (Nat.zero_le _)).congr ?_
  rw [hwalk n j t hS hsym]
  simp only [Nat.sub_zero, hL]

end LogProg

/-- **`UPATH ∈ RL`** [AB09, Theorem 7.19]: a random walk of length `100 n⁴` from `s` decides
undirected connectivity in randomized logarithmic space.

**Proof sketch.** `narm_mem_RL` with the walk machine `upA`, the input-access deciders
(`pathAs_mem`), registers bounded by `200 (|x| + 1)⁴` and `δ = 3/4`. On `x` with a symmetric
layout of `n`, `s`, `t` (`ups_start` with `q` the hitting probability), `x ∈ UPATH` iff `t`
is reachable from `s` (`mem_UPATH_iff`, `ushape_unique`); then the padded graph reaches `t`
too (`padGraph_reflTransGen_iff`), its degree is at most `2n` (`padDegree_le`), and the
hitting probability is at least `3/4` (`three_quarters_le_hitProb`); if `t` is unreachable it
is `0` (`hitProb_eq_zero_of_not_reachable`). On any other `x` (`ups_start` with `q = 0`),
`x ∉ UPATH` and every branch rejects. -/
theorem UPATH_mem_RL : UPATH ∈ Randomized.RL := by
  classical
  refine LogProg.narm_mem_RL LogProg.upA LogProg.ULabel.u0 LogProg.pathAs LogProg.pathAs_mem 200 4
    (δ := 3 / 4) (by norm_num) fun x => ?_
  have h0 : LogProg.UReg.zero.v = fun _ => 0 := by funext r; fin_cases r <;> rfl
  -- the interface from a probability `q` of the machine
  have key : ∀ q : ℚ,
      LogProg.UPS x (200 * (x.length + 1) ^ 4) LogProg.ULabel.u0 LogProg.UReg.zero q →
      (x ∈ UPATH → 3 / 4 ≤ q) → (x ∉ UPATH → q = 0) → ∃ N,
        LogProg.NHalts LogProg.upA LogProg.pathOr x
          (fun a => LogProg.NPreS LogProg.upA x a ∧ ∀ r, a.2.1 r ≤ 200 * (x.length + 1) ^ 4)
          (some LogProg.ULabel.u0, fun _ => 0, none) N ∧
        (x ∈ UPATH → 3 / 4 ≤ LogProg.ansProb LogProg.upA LogProg.pathOr x
          (some LogProg.ULabel.u0, fun _ => 0, none) N true) ∧
        (x ∉ UPATH → LogProg.ansProb LogProg.upA LogProg.pathOr x
          (some LogProg.ULabel.u0, fun _ => 0, none) N false = 1) := by
    intro q hq hin hout
    obtain ⟨N, hN, hacc, hrej⟩ := hq.decides
    rw [h0] at hN hacc hrej
    refine ⟨N, hN.mono fun a ha => ⟨LogProg.upA_npreS x a, ha⟩, fun hx => ?_, fun hx => ?_⟩
    · rw [hacc]; exact hin hx
    · rw [hrej, hout hx]; ring
  by_cases hv : ∃ n s t, UShape x n s t ∧ SymRest x n
  · obtain ⟨n, s, t, hS, hsym⟩ := hv
    refine key ((upGraph x hsym).hitProb ⟨t, hS.2.2.2.2.1⟩ (100 * n ^ 4) ⟨s, hS.2.2.1⟩)
      (LogProg.ups_start x _ (fun h => absurd ⟨n, s, t, hS, hsym⟩ h)
      fun n' s' t' hS' hsym' => ?_) (fun hx => ?_) (fun hx => ?_)
    · obtain ⟨rfl, rfl, rfl⟩ := ushape_unique hS hS'
      rfl
    · obtain ⟨n', s', t', hS', -, hr⟩ := (mem_UPATH_iff x).mp hx
      obtain ⟨rfl, rfl, rfl⟩ := ushape_unique hS hS'
      have hD : Randomized.padDegree n ≤ 2 * Fintype.card (Fin n) := by
        rw [Fintype.card_fin]
        exact Randomized.padDegree_le (lt_of_le_of_lt (Nat.zero_le _) hS.2.2.1)
      have h := (upGraph x hsym).three_quarters_le_hitProb hD
        ((Randomized.padGraph_reflTransGen_iff (symmetric_inEdge hsym) _).mpr hr)
      simpa only [Fintype.card_fin] using h
    · refine (upGraph x hsym).hitProb_eq_zero_of_not_reachable (fun h => hx ?_) _
      exact (mem_UPATH_iff x).mpr ⟨n, s, t, hS, hsym,
        (Randomized.padGraph_reflTransGen_iff (symmetric_inEdge hsym) _).mp h⟩
  · refine key 0 (LogProg.ups_start x 0 (fun _ => rfl) fun n s t hS hsym =>
      absurd ⟨n, s, t, hS, hsym⟩ hv) (fun hx => absurd ?_ hv) (fun _ => rfl)
    obtain ⟨n, s, t, hS, hsym, -⟩ := (mem_UPATH_iff x).mp hx
    exact ⟨n, s, t, hS, hsym⟩

end Complexity
