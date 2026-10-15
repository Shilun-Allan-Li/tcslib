/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.MARMCompile
import TCSlib.Complexity.ClassP.DTIME
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Memory register machines decide in exponential time

The run theorem for memory register machines (`Complexity.LogProg.marm_run`): if the
abstract machine answers `b`, its registers of at most `W` binary digits and its memory head
in `[-P, P]`, then the compiled machine (`Complexity.LogProg.mcompileTM`) answers `b`, every
head staying in its range. The time bound is then a configuration count
(`Complexity.LogProg.runFrom_count_eq`), as for space-bounded machines
([AB09, §4.1.1, proof of Theorem 4.2]): a halting deterministic run never repeats a
configuration. The memory tape is not small, but it only grows — its only symbol is `true`,
and `true` is never overwritten — so along the run its contents are determined by its number
of `true` cells: two configurations of the run with the same small tapes, the same heads
and the same number of memory `1`s are equal. Hence the time is at most
`2 ^ O(W + log n) · P²` (`Complexity.LogProg.marm_dtime`), whatever the number of abstract
steps.

This is infrastructure for [AB09, §4.1.1, Theorem 4.2], not itself a result of the book.

## Main definitions

* `Complexity.LogProg.MGuard` — the guard of the run theorem.

## Main results

* `Complexity.LogProg.marm_run` — the run theorem.
* `Complexity.LogProg.runFrom_count_eq` — a run whose last tape only grows, with heads in
  bounded ranges, halts within the count of its configurations.
* `Complexity.LogProg.marm_dtime` — a correct memory register machine calling logspace
  deciders runs in time `2 ^ O(W + log n) · (P + 1)²`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4, Theorem 4.2.)
-/

namespace Complexity.LogProg

open Turing

/-! ## The run theorem -/

section Run

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The guard of the run theorem: the preconditions of the step (`Pre` of the deterministic
part), register values of at most `W` binary digits (counting one increment), and the memory
head in `[-P, P]`. -/
def MGuard (A : MARM m d Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B W P : ℕ) (x : List Bool) (c : MConf m Λ) : Prop :=
  Pre (A.detPart false) oracle D q0 B x c.1 ∧
    (∀ r, ((Nat.bits (c.1.2.1 r + 1)).length : ℤ) ≤ W) ∧ |c.2.2| ≤ P

/-- **The run theorem for memory register machines.** If, from `(l, v)` with memory `(M, p)`,
the abstract machine halts after `N` steps with answer `b`, every configuration before
satisfying `MGuard`, then the compiled machine, from the compiled configuration having written
`out`, halts with output `out ++ [b]`, staying in the box (`MBox`).

**Proof sketch.** Induction on `N`. A register step is `mdet_live` or `mdet_halt`; a memory
step is one compiled step (`mmem_step`). The runs are concatenated
(`runFrom_forall_append`). -/
theorem marm_run (A : MARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W P : ℕ) :
    ∀ (N : ℕ) (l : Λ) (v : Fin m → ℕ) (M : ℤ → Bool) (p : ℤ) (out : List Bool) (b : Bool),
      (mrun A oracle x ((some l, v, none), (M, p)) N).1.1 = none →
      (mrun A oracle x ((some l, v, none), (M, p)) N).1.2.2 = some b →
      (∀ t < N, MGuard A oracle D q0 B W P x (mrun A oracle x ((some l, v, none), (M, p)) t)) →
      ∃ T, ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) T).state = none ∧
        ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) T).output = out ++ [b] ∧
        ∀ t ≤ T, MBox W B P ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) t) := by
  intro N
  induction N with
  | zero => intro l v M p out b h1; simp [mrun] at h1
  | succ N ih =>
    intro l v M p out b h1 h2 hg
    obtain ⟨hp, hw, hP⟩ := hg 0 (by omega)
    simp only [mrun, Function.iterate_zero, id] at hp hw hP
    rw [mrun_succ] at h1 h2
    have hg' : ∀ c', mstep A oracle x ((some l, v, none), (M, p)) = c' →
        ∀ t < N, MGuard A oracle D q0 B W P x (mrun A oracle x c' t) := by
      intro c' hc t ht
      have := hg (t + 1) (by omega)
      rwa [mrun_succ, hc] at this
    -- a segment to a compiled configuration followed by a halting run
    have compose : ∀ (S : ℕ) (C' : Cfg (m + kD + 1) Bool (CSt (Λ × Ph) SD m) x),
        (mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) S = C' →
        (∀ t ≤ S, MBox W B P ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) t)) →
        (∃ T', ((mcompileTM A l₀ D q0).runFrom C' T').state = none ∧
          ((mcompileTM A l₀ D q0).runFrom C' T').output = out ++ [b] ∧
          ∀ t ≤ T', MBox W B P ((mcompileTM A l₀ D q0).runFrom C' t)) →
        ∃ T, ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) T).state = none ∧
          ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) T).output = out ++ [b] ∧
          ∀ t ≤ T, MBox W B P ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) t) := by
      rintro S C' hS hbS ⟨T', e1, e2, e3⟩
      refine ⟨S + T', by rw [MultiTapeTM.runFrom_add, hS]; exact e1,
        by rw [MultiTapeTM.runFrom_add, hS]; exact e2, runFrom_forall_append hbS ?_⟩
      rw [hS]; exact e3
    cases hA : A l with
    | det i =>
      rcases astep_cases (x := x) (A.detPart false) oracle l v none with ⟨l', v', hs⟩ | ⟨b₀, hs⟩
      · have hm : mstep A oracle x ((some l, v, none), (M, p)) = ((some l', v', none), (M, p)) := by
          rw [mstep_det hA false, hs]
        rw [hm] at h1 h2
        obtain ⟨S, hS, hbS⟩ := mdet_live A l₀ oracle D q0 B W P l l' v v' M p out hs hp hw hP
        exact compose S _ hS hbS (ih l' v' M p out b h1 h2 (hg' _ hm))
      · have hm : mstep A oracle x ((some l, v, none), (M, p)) = ((none, v, some b₀), (M, p)) := by
          rw [mstep_det hA false, hs]
        rw [hm, mrun_halted] at h2
        simp only [Option.some.injEq] at h2
        subst h2
        exact mdet_halt A l₀ oracle D q0 B W P l hA v M p out b₀ hs hp hw hP
    | _ =>
      obtain ⟨l', M', p', hm, hstep⟩ := mmem_step A l₀ oracle D q0 (x := x) (l := l)
        (by simp [hA, MIns.isMem]) v M p out
      rw [hm] at h1 h2
      refine compose 1 _ (by rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
        hstep]) (fun t ht => ?_) (ih l' v M' p' out b h1 h2 (hg' _ hm))
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact mbox_mseam W B P l v M p out hP
      · obtain rfl : t = 1 := by omega
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, hstep]
        cases N with
        | zero => simp [mrun] at h1
        | succ N =>
          exact mbox_mseam W B P l' v M' p' out (hg' _ hm 0 (by omega)).2.2

end Run

/-! ## Counting configurations with a growing tape -/

section Count

variable {K : ℕ} {St : Type} {x : List Bool}

/-- A machine whose transitions write on the last tape only `true` (or nothing) changes each
cell of that tape at most into `true`. -/
lemma step_last_cell (tm : MultiTapeTM (K + 1) Bool St)
    (hwrite : ∀ q a w, ((tm.tr q a w).workTapes (Fin.last K)).1 = none ∨
      ((tm.tr q a w).workTapes (Fin.last K)).1 = some (some true))
    (c : Cfg (K + 1) Bool St x) (z : ℤ) :
    (tm.step c).workTapes (Fin.last K) z = c.workTapes (Fin.last K) z ∨
      (tm.step c).workTapes (Fin.last K) z = some true := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => exact Or.inl rfl
  | some q =>
    simp only [Action.apply]
    rcases hwrite q c.inputSymbol c.workTapeSymbols with h | h
    · left; simp only [h]
    · simp only [h]
      by_cases hz : z = c.workTapePos (Fin.last K)
      · subst hz; right; simp
      · left; simp [Function.update_of_ne hz]

/-- Along a run from initialization, the last tape holds only blanks and `true`s, and a
`true` stays.

**Proof sketch.** Induction on the time, by `step_last_cell`. -/
lemma last_tape_run (tm : MultiTapeTM (K + 1) Bool St)
    (hwrite : ∀ q a w, ((tm.tr q a w).workTapes (Fin.last K)).1 = none ∨
      ((tm.tr q a w).workTapes (Fin.last K)).1 = some (some true)) :
    (∀ t z, (tm.runFrom (tm.initCfg x) t).workTapes (Fin.last K) z = none ∨
      (tm.runFrom (tm.initCfg x) t).workTapes (Fin.last K) z = some true) ∧
    ∀ t t', t ≤ t' → ∀ z, (tm.runFrom (tm.initCfg x) t).workTapes (Fin.last K) z = some true →
      (tm.runFrom (tm.initCfg x) t').workTapes (Fin.last K) z = some true := by
  refine ⟨fun t => ?_, fun t t' htt' z hz => ?_⟩
  · induction t with
    | zero => intro z; left; rfl
    | succ t ih =>
      intro z
      rw [MultiTapeTM.runFrom_succ_eq_step']
      rcases step_last_cell tm hwrite (tm.runFrom (tm.initCfg x) t) z with h | h
      · rw [h]; exact ih z
      · exact Or.inr h
  · obtain ⟨k, rfl⟩ : ∃ k, t' = t + k := ⟨t' - t, by omega⟩
    induction k with
    | zero => exact hz
    | succ k ih =>
      rw [← Nat.add_assoc, MultiTapeTM.runFrom_succ_eq_step']
      rcases step_last_cell tm hwrite (tm.runFrom (tm.initCfg x) (t + k)) z with h | h
      · rw [h]; exact ih (by omega)
      · exact h

open MultiTapeTM.ConfigCount in
/-- **A run whose last tape only grows halts within its configuration count.** If the
transitions of `tm` write on the last tape only `true`, and the run from initialization has
halted by time `T` with every head of the other tapes in `[-B, B]` and the head of the last
tape in `[-P, P]` up to then, then the run is already at its final configuration at time
`(|St| + 1) (n + 2) 3 ^ (K (2B + 1)) (2B + 1) ^ K (2P + 1) (2P + 2)`.

**Proof sketch.** Before the first halting time no core repeats (`core_injOn`). Code a
configuration by its state, input position, the other tapes on `[-B, B]`, the heads, and the
number of `true` cells of the last tape in `[-P, P]`; nonblank cells lie in the head ranges
(`mem_visited_of_ne_none`). Along the run the last tape only grows (`last_tape_run`), so of
two times, the earlier tape is contained in the later; with equal counts they are equal. So
the code is injective before the halting time, which is therefore at most the number of
codes. -/
theorem runFrom_count_eq [Fintype St] (tm : MultiTapeTM (K + 1) Bool St) (B P T : ℕ)
    (hwrite : ∀ q a w, ((tm.tr q a w).workTapes (Fin.last K)).1 = none ∨
      ((tm.tr q a w).workTapes (Fin.last K)).1 = some (some true))
    (hT : (tm.runFrom (tm.initCfg x) T).state = none)
    (hbox : ∀ t ≤ T, (∀ i : Fin K, |(tm.runFrom (tm.initCfg x) t).workTapePos i.castSucc| ≤ B) ∧
      |(tm.runFrom (tm.initCfg x) t).workTapePos (Fin.last K)| ≤ P) :
    tm.runFrom (tm.initCfg x) ((Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
      (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2))) = tm.runFrom (tm.initCfg x) T := by
  classical
  set run := fun t => tm.runFrom (tm.initCfg x) t with hrun
  have hex : ∃ t, (run t).state = none := ⟨T, hT⟩
  set T₀ := Nat.find hex with hT₀
  have hT0 : (run T₀).state = none := Nat.find_spec hex
  have hT0T : T₀ ≤ T := Nat.find_min' hex hT
  have hmin : ∀ t < T₀, (run t).state ≠ none := fun t ht => Nat.find_min hex ht
  obtain ⟨hcells, hmono⟩ := last_tape_run (x := x) tm hwrite
  -- nonblank cells lie in the head ranges
  have hwin : ∀ t ≤ T, ∀ (i : Fin (K + 1)) (z : ℤ), (run t).workTapes i z ≠ none →
      ∃ t' ≤ t, (run t').workTapePos i = z := by
    intro t ht i z hz
    have := MultiTapeTM.mem_visited_of_ne_none tm x t i z hz
    simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at this
    obtain ⟨t', ht', e⟩ := this
    exact ⟨t', by omega, e⟩
  have hwinS : ∀ t ≤ T, ∀ (i : Fin K) (z : ℤ), (run t).workTapes i.castSucc z ≠ none →
      |z| ≤ B := by
    intro t ht i z hz
    obtain ⟨t', ht', rfl⟩ := hwin t ht _ z hz
    exact (hbox t' (by omega)).1 i
  have hwinL : ∀ t ≤ T, ∀ z : ℤ, (run t).workTapes (Fin.last K) z ≠ none → |z| ≤ P := by
    intro t ht z hz
    obtain ⟨t', ht', rfl⟩ := hwin t ht _ z hz
    exact (hbox t' (by omega)).2
  -- the code
  let cnt : ℕ → Finset ℤ := fun t =>
    (Finset.Icc (-(P : ℤ)) P).filter fun z => (run t).workTapes (Fin.last K) z = some true
  have hcnt : ∀ t, (cnt t).card ≤ 2 * P + 1 := by
    intro t
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    rw [Int.card_Icc]; omega
  let code : ℕ → Option St × Fin (x.length + 2) × (Fin K → Fin (2 * B + 1) → Option Bool) ×
      (Fin K → Fin (2 * B + 1)) × Fin (2 * P + 1) × Fin (2 * P + 2) := fun t =>
    ((run t).state, (run t).inputPos,
      fun i j => (run t).workTapes i.castSucc ((j : ℤ) - B),
      fun i => posCode B ((run t).workTapePos i.castSucc),
      posCode P ((run t).workTapePos (Fin.last K)),
      ⟨(cnt t).card, by have := hcnt t; omega⟩)
  -- equal codes at two times give equal cores
  have hcore : ∀ a b, a ≤ b → b ≤ T → code a = code b → core (run a) = core (run b) := by
    intro a b hab hb h
    simp only [code, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨hs, hi, hw, hp, hpl, hc⟩ := h
    simp only [core, Prod.mk.injEq]
    refine ⟨hs, hi, ?_, ?_⟩
    · funext i z
      refine Fin.lastCases ?_ (fun j => ?_) i
      · -- the memory tape
        have hsub : cnt a ⊆ cnt b := by
          intro z hz
          simp only [cnt, Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, hmono a b hab z hz.2⟩
        have heq : cnt a = cnt b := Finset.eq_of_subset_of_card_le hsub (le_of_eq hc.symm)
        by_cases hz : |z| ≤ P
        · have hzI : z ∈ Finset.Icc (-(P : ℤ)) P := by
            rw [Finset.mem_Icc]; rw [abs_le] at hz; exact hz
          have hiff : (run a).workTapes (Fin.last K) z = some true ↔
              (run b).workTapes (Fin.last K) z = some true := by
            have := congrArg (fun s => z ∈ s) heq
            simpa [cnt, hzI] using this
          rcases hcells a z with ha | ha <;> rcases hcells b z with hb' | hb'
          · rw [ha, hb']
          · exact absurd (hiff.mpr hb') (by rw [ha]; simp)
          · exact absurd (hiff.mp ha) (by rw [hb']; simp)
          · rw [ha, hb']
        · have h1 : (run a).workTapes (Fin.last K) z = none := by
            by_contra hne; exact hz (hwinL a (by omega) z hne)
          have h2 : (run b).workTapes (Fin.last K) z = none := by
            by_contra hne; exact hz (hwinL b hb z hne)
          rw [h1, h2]
      · by_cases hz : |z| ≤ B
        · have := congrFun (congrFun hw j) ⟨(z + B).toNat, by rw [abs_le] at hz; omega⟩
          simp only at this
          rwa [show (((z + B).toNat : ℕ) : ℤ) - B = z by rw [abs_le] at hz; omega] at this
        · have h1 : (run a).workTapes j.castSucc z = none := by
            by_contra hne; exact hz (hwinS a (by omega) j z hne)
          have h2 : (run b).workTapes j.castSucc z = none := by
            by_contra hne; exact hz (hwinS b hb j z hne)
          rw [h1, h2]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact posCode_injOn P (hbox a (by omega)).2 (hbox b hb).2 hpl
      · exact posCode_injOn B ((hbox a (by omega)).1 j) ((hbox b hb).1 j) (congrFun hp j)
  have hinj : Set.InjOn code (Finset.range T₀ : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact core_injOn tm _ T₀ hT0 hmin h' hb (hcore a b h'.le (by omega) hab)
    · exact core_injOn tm _ T₀ hT0 hmin h' ha (hcore b a h'.le (by omega) hab.symm)
  have hcard : T₀ ≤ (Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
      (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2)) := by
    have := Finset.card_le_card_of_injOn code (fun a _ => Finset.mem_univ _) hinj
    simp only [Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_option,
      Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Fintype.card_bool] at this
    refine this.trans (le_of_eq ?_)
    rw [← pow_mul, Nat.mul_comm (2 * B + 1) K]
    ring
  rw [show (Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
      (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2)) =
      T₀ + ((Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
      (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2)) - T₀) by omega,
    MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hT0,
    show T = T₀ + (T - T₀) by omega, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hT0]

end Count

/-! ## From memory register machines to deterministic time -/

section Bridge

/-- The configuration count of `runFrom_count_eq` for the compiled machine, in exponential
form. Here `q + 1` bounds the states, `K` is the number of small tapes, the register heads lie
in `[-1, W]` and the decider heads in `[-B, B]` with `B` the logspace range of the virtual
inputs (`length_callSegs_le`).

**Proof sketch.** The virtual input length `y = 2n + 2 + m (2W + 2)` is below
`2 ^ (logSpace n + W + m + 3)`, so `logSpace y ≤ logSpace n + W + m + 3` and the small-tape
range is at most `(cs + 1) (m + 3) u` with `u = W + logSpace n + 1`. Bound `3 ≤ 2 ^ 2`,
`X ≤ 2 ^ X`, `n + 2 ≤ 2 ^ (logSpace n + 1)` and `(2P + 1) (2P + 2) ≤ 4 (P + 1) ^ 2`, and
collect the exponents. -/
private lemma count_bound (q n K W cs m P : ℕ) :
    (q + 1) * (n + 2) *
        3 ^ (K * (2 * (W + 1 + (cs * logSpace (2 * n + 2 + m * (2 * W + 2)) + 1)) + 1)) *
        (2 * (W + 1 + (cs * logSpace (2 * n + 2 + m * (2 * W + 2)) + 1)) + 1) ^ K *
        ((2 * P + 1) * (2 * P + 2)) ≤
      2 ^ ((q + 4 + 3 * K * (2 * ((cs + 1) * (m + 3)) + 1)) * (W + logSpace n + 1)) *
        (P + 1) ^ 2 := by
  set L := logSpace n with hL
  set y := 2 * n + 2 + m * (2 * W + 2) with hy
  have hn : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hW : W + 1 ≤ 2 ^ W := Nat.lt_two_pow_self (n := W)
  have hm : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self (n := m)
  have hL1 : 1 ≤ L := by simp [hL, logSpace]
  -- the logarithm of the virtual input length
  have hylog : logSpace y ≤ L + W + m + 3 := by
    have h1 : y ≤ 4 * ((n + 1) * (W + 1) * (m + 1)) := by
      have a1 : n + 1 ≤ (n + 1) * (W + 1) * (m + 1) := by
        calc n + 1 = (n + 1) * 1 * 1 := by ring
          _ ≤ (n + 1) * (W + 1) * (m + 1) := by gcongr <;> omega
      have a2 : m * (W + 1) ≤ (n + 1) * (W + 1) * (m + 1) := by
        calc m * (W + 1) = 1 * (W + 1) * m := by ring
          _ ≤ (n + 1) * (W + 1) * (m + 1) := by gcongr <;> omega
      have e : y = 2 * (n + 1) + 2 * (m * (W + 1)) := by simp only [hy]; ring
      omega
    have h2 : (n + 1) * (W + 1) * (m + 1) ≤ 2 ^ L * 2 ^ W * 2 ^ m := by gcongr
    have h3 : y < 2 ^ (L + W + m + 3) := by
      have : 2 ^ (L + W + m + 3) = 8 * (2 ^ L * 2 ^ W * 2 ^ m) := by
        rw [pow_add, pow_add, pow_add]; ring
      have hpos : 0 < 2 ^ L * 2 ^ W * 2 ^ m :=
        Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos L) (Nat.two_pow_pos W)) (Nat.two_pow_pos m)
      omega
    have h4 := Nat.log_lt_of_lt_pow (b := 2) (by omega : y ≠ 0) h3
    simp only [logSpace]
    omega
  -- the small-tape range
  set E := (cs + 1) * (m + 3) with hE
  set u := W + L + 1 with hu
  have hu1 : 1 ≤ u := by omega
  have hB : W + 1 + (cs * logSpace y + 1) ≤ E * u := by
    have h1 : cs * logSpace y ≤ cs * (L + W + m + 3) := Nat.mul_le_mul_left _ hylog
    have h2 : L + W + m + 3 ≤ (m + 3) * u := by
      have : (m + 3) * u = u + (m + 2) * u := by ring
      have : m + 2 ≤ (m + 2) * u := Nat.le_mul_of_pos_right _ hu1
      omega
    have h3 : (cs + 1) * (L + W + m + 3) ≤ E * u := by
      rw [hE, mul_assoc]; exact Nat.mul_le_mul_left _ h2
    have : (cs + 1) * (L + W + m + 3) = cs * (L + W + m + 3) + (L + W + m + 3) := by ring
    omega
  set X := 2 * (W + 1 + (cs * logSpace y + 1)) + 1 with hX
  have hXu : X ≤ (2 * E + 1) * u := by
    have : (2 * E + 1) * u = 2 * (E * u) + u := by ring
    omega
  -- the factors
  have f1 : q + 1 ≤ 2 ^ (q + 1) := (Nat.lt_two_pow_self (n := q + 1)).le
  have f2 : n + 2 ≤ 2 ^ (L + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := L); omega
  have f3 : 3 ^ (K * X) ≤ 2 ^ (2 * (K * X)) := by
    calc 3 ^ (K * X) ≤ (2 ^ 2) ^ (K * X) := Nat.pow_le_pow_left (by decide) _
      _ = 2 ^ (2 * (K * X)) := (pow_mul 2 2 _).symm
  have f4 : X ^ K ≤ 2 ^ (X * K) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := X)).le _
  have f5 : (2 * P + 1) * (2 * P + 2) ≤ 2 ^ 2 * (P + 1) ^ 2 :=
    calc (2 * P + 1) * (2 * P + 2) ≤ (2 * P + 2) * (2 * P + 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 2 * (P + 1) ^ 2 := by ring
  have hexp : (q + 1) + (L + 1) + 2 * (K * X) + X * K + 2 ≤
      (q + 4 + 3 * K * (2 * E + 1)) * u := by
    have g1 : 3 * (K * X) ≤ 3 * K * ((2 * E + 1) * u) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXu)
    have g2 : (q + 4) + L ≤ (q + 4) * u := by
      have g2a : L ≤ (q + 4) * L := Nat.le_mul_of_pos_left L (by omega)
      have g2b : (q + 4) * (L + 1) ≤ (q + 4) * u := Nat.mul_le_mul_left _ (by omega)
      have g2c : (q + 4) * (L + 1) = (q + 4) * L + (q + 4) := by ring
      omega
    have e : (q + 4 + 3 * K * (2 * E + 1)) * u = (q + 4) * u + 3 * K * ((2 * E + 1) * u) := by
      ring
    have e2 : X * K = K * X := Nat.mul_comm _ _
    omega
  calc (q + 1) * (n + 2) * 3 ^ (K * X) * X ^ K * ((2 * P + 1) * (2 * P + 2))
      ≤ 2 ^ (q + 1) * 2 ^ (L + 1) * 2 ^ (2 * (K * X)) * 2 ^ (X * K) *
          (2 ^ 2 * (P + 1) ^ 2) := by gcongr
    _ = 2 ^ ((q + 1) + (L + 1) + 2 * (K * X) + X * K + 2) * (P + 1) ^ 2 := by
      rw [pow_add, pow_add, pow_add, pow_add]; ring
    _ ≤ 2 ^ ((q + 4 + 3 * K * (2 * E + 1)) * u) * (P + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hexp)

variable {m d : ℕ} {Λ : Type}

/-- **Memory register machines decide in exponential time.** If, on every input `x`, the
memory register machine `A` (calling deciders for languages in `L`), started at `l₀` with all
registers `0` and a blank memory, answers `x ∈ L` through configurations meeting the syntactic
preconditions, with register values of at most `W |x|` binary digits (counting one increment)
and the memory head in `[-P |x|, P |x|]`, then some machine decides `L` on every input `x`
within `2 ^ (C (W |x| + logSpace |x| + 1)) · (P |x| + 1)²` steps.

**Proof sketch.** As for `arm_decides`: the deciders are collected in a clean bank
(`bank_cleanRun`), whose head ranges on the virtual inputs (of length at most
`2|x| + 2 + m (2W + 2)`, `length_callSegs_le`) are logarithmic. `marm_run` gives a halting
compiled run in the box, and `runFrom_count_eq` (the compiled machine writes only `true` on its
memory tape) bounds its halting time by the configuration count, which `count_bound` puts in
exponential form. -/
theorem marm_dtime {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : MARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (W P : ℕ → ℕ)
    (hcorr : ∀ x, MHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun c => PreS (A.detPart false) x c.1 ∧
        (∀ r, (Nat.bits (c.1.2.1 r + 1)).length ≤ W x.length) ∧ |c.2.2| ≤ (P x.length : ℤ))
      ((some l₀, fun _ => 0, none), (fun _ => false, 0))
      (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    ∃ (M : FinTM Bool) (C : ℕ), ∀ x, M.ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x]
      (2 ^ (C * (W x.length + logSpace x.length + 1)) * (P x.length + 1) ^ 2) := by
  classical
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  let c : Fin d → ℕ := fun j => Classical.choose (hc j)
  let Ms : Fin d → FinTM Bool := fun j => Classical.choose (Classical.choose_spec (hc j))
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) fun n => c j * logSpace n :=
    fun j => Classical.choose_spec (Classical.choose_spec (hc j))
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  set q := Fintype.card (CSt (Λ × Ph) (CleanSt (BankS Ms) (bankK Ms)) m) with hq
  refine ⟨mcompileFinTM A l₀ (bankTM Ms) (bankStart Ms),
    q + 4 + 3 * (m + (bankK Ms + bankK Ms)) * (2 * ((cs + 1) * (m + 3)) + 1), fun x => ?_⟩
  set n := x.length with hn
  set Wn := W n with hWn
  set Pn := P n with hPn
  set B := cs * logSpace (2 * n + 2 + m * (2 * Wn + 2)) + 1 with hB
  obtain ⟨N, h1, h2, hm⟩ := hcorr x
  have hguard : ∀ t < N, MGuard A oracle (bankTM Ms) (bankStart Ms) B Wn Pn x
      (mrun A oracle x ((some l₀, fun _ => 0, none), (fun _ => false, 0)) t) := by
    intro t ht
    obtain ⟨hps, hbd, hp⟩ := hm t ht
    refine ⟨?_, fun r => by exact_mod_cast hbd r, hp⟩
    generalize hat : (mrun A oracle x ((some l₀, fun _ => 0, none), (fun _ => false, 0)) t).1 =
      a at hps hbd
    rcases a with ⟨_ | l, v, res⟩
    · trivial
    · simp only [Pre]
      cases hA : A.detPart false l with
      | jeq r s' l₁ l₀' => simpa [PreS, hA] using hps
      | jeqIn r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqFst r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqSnd r l₁ l₀' => simpa [PreS, hA] using hps
      | inc => trivial
      | dec => trivial
      | clr => trivial
      | half => trivial
      | jz => trivial
      | jodd => trivial
      | ret => trivial
      | valP => trivial
      | valQ => trivial
      | call j md args l₁ l₀' =>
      simp only [PreS, hA] at hps
      refine ⟨hps, ?_⟩
      refine cleanRun_mono (bank_cleanRun Ms As (fun j n => c j * logSpace n) hMs j _) ?_
      have hVl := length_callSegs_le (x := x) ⟨j, md, args, l₁, l₀'⟩ Wn (fun r => Nat.bits (v r))
        (fun r => by
          show (Nat.bits (v r)).length ≤ Wn
          have h0 : (Nat.bits (v r + 1)).length ≤ Wn := hbd r
          have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length :=
            length_bits_mono (by omega)
          omega) hps
      rw [← hn] at hVl
      have hlog : logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
          fun r => Nat.bits (v r))).length ≤ logSpace (2 * n + 2 + m * (2 * Wn + 2)) := by
        simp only [logSpace]
        have := Nat.log_mono_right (b := 2) hVl
        omega
      have hcm : c j * logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
          fun r => Nat.bits (v r))).length ≤ cs * logSpace (2 * n + 2 + m * (2 * Wn + 2)) :=
        Nat.mul_le_mul (hcj j) hlog
      show max _ 1 ≤ B
      exact max_le (hcm.trans (by omega)) (by omega)
  obtain ⟨T, e1, e2, e3⟩ := marm_run (x := x) A l₀ oracle (bankTM Ms) (bankStart Ms) B Wn Pn N l₀
    (fun _ => 0) (fun _ => false) 0 [] (MultiTapeTM.indicator (L : Set (List Bool)) x) h1 h2
    hguard
  rw [← mcompileTM_init] at e1 e2 e3
  simp only [List.nil_append] at e2
  have hcount := runFrom_count_eq (K := m + (bankK Ms + bankK Ms)) (x := x)
    (mcompileTM A l₀ (bankTM Ms) (bankStart Ms))
    (Wn + 1 + B) Pn T
    (fun q' a w => by
      simp only [mcompileTM]
      cases mop A q' with
      | none => left; simp [liftAct]
      | some i => cases i <;> simp [memAct])
    e1
    (fun t ht => by
      obtain ⟨b1, b2, b3⟩ := e3 t ht
      refine ⟨fun i => ?_, b3⟩
      refine Fin.addCases (fun r => ?_) (fun k => ?_) i
      · have := b1 r
        rw [abs_le]; constructor <;> push_cast <;> omega
      · have := b2 k
        rw [abs_le] at this ⊢; constructor <;> push_cast <;> omega)
  rw [FinTM.computesInTime_iff]
  have hb := count_bound q n (m + (bankK Ms + bankK Ms)) Wn cs m Pn
  refine ⟨?_, ?_⟩
  · show ((mcompileTM A l₀ (bankTM Ms) (bankStart Ms)).runFrom
      ((mcompileTM A l₀ (bankTM Ms) (bankStart Ms)).initCfg x) _).state = none
    rw [← Nat.add_sub_of_le hb, MultiTapeTM.runFrom_add, hcount, MultiTapeTM.runFrom_of_halt _ e1]
    exact e1
  · show ((mcompileTM A l₀ (bankTM Ms) (bankStart Ms)).runFrom
      ((mcompileTM A l₀ (bankTM Ms) (bankStart Ms)).initCfg x) _).output = _
    rw [← Nat.add_sub_of_le hb, MultiTapeTM.runFrom_add, hcount, MultiTapeTM.runFrom_of_halt _ e1]
    exact e2

end Bridge

end Complexity.LogProg
