/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SpaceAmplify

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Repeating a space-bounded PTM: independence and space

The analysis of `Randomized.Amplify.amp` [AB09, §7.7, p. 139]. Induction on the number of runs
left, composing each run of `N` with its continuation (`Randomized.Amplify.randProb_comp`),
shows that the runs behave as independent blocks of `T` coins; the work heads stay within the
range of a single run of `N`.

## Main definitions

* `Randomized.Amplify.acc` — acceptance of `N` on a block of coins.
* `Randomized.Amplify.val` — the distribution of `dec` of the number of accepting blocks.

## Main results

* `Randomized.Amplify.amp_haltsWithin`, `Randomized.Amplify.amp_outputProb` — the output is
  `[v]` with the probability that `dec` of the number of accepting blocks among `r + 1`
  independent blocks of `T` coins is `v`.
* `Randomized.Amplify.majority_randProb_ge` — the majority of `2n + 1` blocks is correct with
  probability at least `1 - 2 (1 - 4ε²)^n`.
* `Randomized.Amplify.amp_usesSpace` — every branch uses at most `(r + 1) k (2 S + 1)` cells.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.Amplify

open Turing Complexity Complexity.LogProg

variable {N : FinNDTM Bool} {r : ℕ} {dec : ℕ → Bool} {x : List Bool}

/-! ### Halting and the output distribution -/

/-- Halting by length `n` persists for longer words (`Turing.NDTM.HaltsWithin.mono` from an
arbitrary configuration). -/
theorem halted_of_le {K : ℕ} {St : Type} {M : NDTM K Bool St} {C : Cfg K Bool St x} {n : ℕ}
    (h : ∀ w : List Bool, w.length = n → (M.runWith w C).state = none)
    {w : List Bool} (hw : n ≤ w.length) : (M.runWith w C).state = none := by
  have hn := h (w.take n) (List.length_take_of_le hw)
  rw [← List.take_append_drop n w, NDTM.runWith_append, NDTM.runWith_of_halt _ hn]
  exact hn

/-- The count does not reach the cap. -/
theorem bump_val {c : Fin (r + 2)} (hc : c.val ≤ r) (b : Bool) :
    (bump c b).val = c.val + if b then 1 else 0 := by
  cases b
  · simp [bump]
  · simp [bump]
    omega

/-- The acceptance test of one run: the length-`T` coin block makes `N` output `[true]`. -/
def acc (N : FinNDTM Bool) (x : List Bool) (l : List Bool) : Bool :=
  decide (N.outputWith x l = [true])

/-- The probability that `dec` of `c` plus the number of accepting blocks among `i`
independent blocks of `T` coins is `v`. -/
def val (N : FinNDTM Bool) (x : List Bool) (T : ℕ) (dec : ℕ → Bool) (i c : ℕ) (v : Bool) : ℚ :=
  randProb (i * T) fun l => dec (c + blockCount T i (acc N x) l) = v

/-- With no blocks left the outcome is `dec c`. -/
theorem val_zero (T c : ℕ) (v : Bool) :
    val N x T dec 0 c v = if dec c = v then 1 else 0 := by
  unfold val
  rw [zero_mul, ← randProb_const 0 (dec c = v)]
  exact randProb_congr fun r => by simp [blockCount]

/-- Conditioning on the first block.

**Proof sketch.** Split the `(i + 1) T` coins into the first block and the rest (`blockCount_succ`):
the event is the disjoint union of "first block accepts and the rest gives `dec (c + 1 + ·) = v`"
and "first block rejects and the rest gives `dec (c + ·) = v`"; each part factors
(`randProb_split`). -/
theorem val_succ (T i c : ℕ) (v : Bool) :
    val N x T dec (i + 1) c v =
      randProb T (fun l => acc N x l = true) * val N x T dec i (c + 1) v +
        (1 - randProb T (fun l => acc N x l = true)) * val N x T dec i c v := by
  unfold val
  rw [show (i + 1) * T = T + i * T by ring]
  have hev : randProb (T + i * T) (fun l => dec (c + blockCount T (i + 1) (acc N x) l) = v) =
      randProb (T + i * T) (fun l =>
        ((fun l' => acc N x l' = true) (l.take T) ∧
          (fun w => dec (c + 1 + blockCount T i (acc N x) w) = v) (l.drop T)) ∨
        ((fun l' => acc N x l' = false) (l.take T) ∧
          (fun w => dec (c + blockCount T i (acc N x) w) = v) (l.drop T))) :=
    randProb_congr fun r => by
      rw [blockCount_succ]
      rcases hb : acc N x ((List.ofFn r).take T) <;> simp [hb, Nat.add_assoc]
  rw [hev, randProb_or_disjoint _ _ (fun r => by
      rintro ⟨⟨h1, -⟩, h2, -⟩
      rw [h1] at h2
      exact absurd h2 (by simp)),
    randProb_split T (i * T) (fun l' => acc N x l' = true)
      (fun w => dec (c + 1 + blockCount T i (acc N x) w) = v),
    randProb_split T (i * T) (fun l' => acc N x l' = false)
      (fun w => dec (c + blockCount T i (acc N x) w) = v), randProb_bool_false]

/-- The acceptance bit of a simulated run. -/
def accBit (u : Cfg N.k Bool N.State x) : Bool := decide (summ u.output = some true)

/-- The acceptance bit of a run from the start is `acc`. -/
theorem accBit_runWith (l : List Bool) :
    accBit (N.tm.runWith l (N.tm.initCfg x)) = acc N x l := by
  simp only [accBit, acc, summ_eq_some_true, FinNDTM.outputWith]

variable {T : ℕ}

/-- **One run, then the rest.** If after run `j` the machine halts within `m` from every
rewinding configuration, then from the start of run `j` it halts within `T + m`. -/
theorem run_halts (hT : N.tm.HaltsWithin x T) {j : Fin (r + 1)} (c : Fin (r + 2))
    {D : ACfg N r x} (hD : Fresh D j.val) {m : ℕ}
    (ih : ∀ (c' : Fin (r + 2)) (C : ACfg N r x), RewindAt C j c' →
      ∀ w : List Bool, w.length = m → ((amp N r dec).tm.runWith w C).state = none) :
    ∀ w : List Bool, w.length = T + m →
      ((amp N r dec).tm.runWith w (emb D j c (N.tm.initCfg x))).state = none :=
  halts_comp (fun u b hu => step_emb D j c u b hu)
    (fun _ hu w hw => ih _ _ (rewindAt_emb c hu hD) w hw) T _ hT

/-- **One run, then the rest**, in probability: if after run `j` the output distribution is
`val i`, then from the start of run `j` it is `val (i + 1)`.

**Proof sketch.** Apply `randProb_comp` with `φ := emb D j c`, the acceptance bit `accBit`, and `g b
:= val i (c + [b])`: the value after a halted run is the hypothesis `ih` at the rewinding
configuration `rewindAt_emb`, whose count is `c + [b]` (`bump_val`). The two weights are `Pr[acc]`
and `1 - Pr[acc]` (`accBit_runWith`), and `val_succ` recombines them. -/
theorem run_prob (hT : N.tm.HaltsWithin x T) (v : Bool) {i : ℕ} {j : Fin (r + 1)}
    (hj : j.val + i = r) {c : Fin (r + 2)} (hc : c.val ≤ j.val) {D : ACfg N r x}
    (hD : Fresh D j.val)
    (hh : ∀ (c' : Fin (r + 2)) (C : ACfg N r x), RewindAt C j c' →
      ∀ w : List Bool, w.length = i * (T + x.length + 2) + 1 →
        ((amp N r dec).tm.runWith w C).state = none)
    (ih : ∀ (c' : Fin (r + 2)) (C : ACfg N r x), RewindAt C j c' → c'.val ≤ j.val + 1 →
      randProb (i * (T + x.length + 2) + 1)
        (fun w => ((amp N r dec).tm.runWith w C).output = [v]) = val N x T dec i c'.val v) :
    randProb (T + (i * (T + x.length + 2) + 1))
        (fun w => ((amp N r dec).tm.runWith w (emb D j c (N.tm.initCfg x))).output = [v]) =
      val N x T dec (i + 1) c.val v := by
  rw [randProb_comp (fun u b hu => step_emb D j c u b hu)
    (fun u hu w hw => hh _ _ (rewindAt_emb c hu hD) w hw) (fun C => C.output = [v]) accBit
    (fun b => val N x T dec i (c.val + if b then 1 else 0) v)
    (fun u hu => by
      rw [ih _ _ (rewindAt_emb c hu hD) (by rw [bump_val (by omega)]; split <;> omega),
        bump_val (by omega)]
      rfl) T _ hT, val_succ]
  have e1 : randProb T (fun u => accBit (N.tm.runWith u (N.tm.initCfg x)) = true) =
      randProb T (fun l => acc N x l = true) :=
    randProb_congr fun r => by rw [accBit_runWith]
  have e0 : randProb T (fun u => accBit (N.tm.runWith u (N.tm.initCfg x)) = false) =
      1 - randProb T (fun l => acc N x l = true) := by
    rw [← randProb_bool_false]
    exact randProb_congr fun r => by rw [accBit_runWith]
  rw [e1, e0]
  simp

/-- From a rewinding configuration after run `j` with `i = r - j` runs left, every branch
halts within `i (T + |x| + 2) + 1` steps.

**Proof sketch.** Induction on `i`. With no run left, one step emits the decision and halts
(`rewind_last`). Otherwise rewinding takes `p + 2 ≤ |x| + 2` steps to restart run `j + 1` on a fresh
block (`rewind_run`, `restart_eq_emb`); from there `run_halts` with the induction hypothesis bounds
the rest by `T + (i (T + |x| + 2) + 1)`, and longer words stay halted (`halted_of_le`). -/
theorem rewind_halts (hT : N.tm.HaltsWithin x T) :
    ∀ (i : ℕ) (j : Fin (r + 1)), j.val + i = r → ∀ (c : Fin (r + 2)) (C : ACfg N r x),
      RewindAt C j c → ∀ w : List Bool, w.length = i * (T + x.length + 2) + 1 →
        ((amp N r dec).tm.runWith w C).state = none := by
  intro i
  induction i with
  | zero =>
    intro j hj c C hC w hw
    obtain ⟨b, w', rfl⟩ : ∃ b w', w = b :: w' := by
      cases w with
      | nil => simp at hw
      | cons b w' => exact ⟨b, w', rfl⟩
    have hlast : ¬ j.val < r := by omega
    cases b
    · rw [(rewind_last hC.1 hlast w').2]; rfl
    · rw [(rewind_last hC.1 hlast w').1]; rfl
  | succ i ih =>
    intro j hj c C hC w hw
    have hjr : j.val < r := by omega
    obtain ⟨p, hp, -, hrun⟩ := rewind_run (dec := dec) hC.1 hjr
    have hE := restart_eq_emb C ⟨j.val + 1, by omega⟩ c
      (fun t ht => hC.2.2 t (by rw [ht]; exact Nat.lt_succ_self _)) hC.2.1
    have hF : Fresh (restart C ⟨j.val + 1, by omega⟩ c) (j.val + 1) :=
      fun t ht => hC.2.2 t (by omega)
    have hcomp := run_halts (dec := dec) (j := ⟨j.val + 1, by omega⟩) hT c hF
      (ih (⟨j.val + 1, by omega⟩ : Fin (r + 1)) (by show j.val + 1 + i = r; omega))
    have hmul : (i + 1) * (T + x.length + 2) = i * (T + x.length + 2) + (T + x.length + 2) := by
      ring
    rw [← List.take_append_drop (p + 2) w, NDTM.runWith_append,
      hrun _ (List.length_take_of_le (by omega)), hE]
    exact halted_of_le hcomp (by simp only [List.length_drop]; omega)

/-- From a rewinding configuration after run `j` with `i = r - j` runs left and count `c`,
the output is `[v]` with probability `val i c v`.

**Proof sketch.** Induction on `i`, along `rewind_halts`. With no run left the output is `[dec c]`
on every branch (`randProb_runWith_const`, `val_zero`). Otherwise the `p + 2` rewinding steps are
forced (`randProb_runWith_seg`), the remaining coins beyond the halting bound are irrelevant
(`randProb_runWith_mono`), and `run_prob` with the induction hypothesis gives `val (i + 1) c v`. -/
theorem rewind_prob (hT : N.tm.HaltsWithin x T) (v : Bool) :
    ∀ (i : ℕ) (j : Fin (r + 1)), j.val + i = r → ∀ (c : Fin (r + 2)) (C : ACfg N r x),
      RewindAt C j c → c.val ≤ j.val + 1 →
        randProb (i * (T + x.length + 2) + 1)
          (fun w => ((amp N r dec).tm.runWith w C).output = [v]) = val N x T dec i c.val v := by
  intro i
  induction i with
  | zero =>
    intro j hj c C hC _
    have hlast : ¬ j.val < r := by omega
    rw [zero_mul, zero_add, randProb_runWith_const (Cf := finish dec C c) (S := 1) (fun u hu => ?_)
      (fun D => D.output = [v]), val_zero]
    · simp [finish, hC.2.1]
    · obtain ⟨b, rfl⟩ : ∃ b, u = [b] := by
        match u, hu with
        | [b], _ => exact ⟨b, rfl⟩
      cases b
      · exact (rewind_last hC.1 hlast []).2
      · exact (rewind_last hC.1 hlast []).1
  | succ i ih =>
    intro j hj c C hC hc
    have hjr : j.val < r := by omega
    obtain ⟨p, hp, -, hrun⟩ := rewind_run (dec := dec) hC.1 hjr
    have hE := restart_eq_emb C ⟨j.val + 1, by omega⟩ c
      (fun t ht => hC.2.2 t (by rw [ht]; exact Nat.lt_succ_self _)) hC.2.1
    have hF : Fresh (restart C ⟨j.val + 1, by omega⟩ c) (j.val + 1) :=
      fun t ht => hC.2.2 t (by omega)
    have hh := rewind_halts (dec := dec) hT i (⟨j.val + 1, by omega⟩ : Fin (r + 1))
      (by show j.val + 1 + i = r; omega)
    have hcomp := run_halts (dec := dec) (j := ⟨j.val + 1, by omega⟩) hT c hF hh
    have hmul : (i + 1) * (T + x.length + 2) = i * (T + x.length + 2) + (T + x.length + 2) := by
      ring
    have hlen : (i + 1) * (T + x.length + 2) + 1 =
        (p + 2) + ((i + 1) * (T + x.length + 2) + 1 - (p + 2)) := by omega
    rw [hlen, randProb_runWith_seg hrun _ (fun D => D.output = [v]), hE,
      randProb_runWith_mono hcomp (by omega) (fun D => D.output = [v])]
    exact run_prob hT v (j := ⟨j.val + 1, by omega⟩) (by show j.val + 1 + i = r; omega)
      (by show c.val ≤ j.val + 1; omega) hF hh
      (ih (⟨j.val + 1, by omega⟩ : Fin (r + 1)) (by show j.val + 1 + i = r; omega))

/-- No block after the first is touched at the start. -/
theorem fresh_init : Fresh ((amp N r dec).tm.initCfg x) 0 := fun _ _ => ⟨rfl, rfl⟩

/-- **The repeated machine halts**: if `N` halts on `x` within `T` on every branch, then
`amp N r dec` halts within `T + r (T + |x| + 2) + 1`. [AB09, §7.7, p. 139] -/
theorem amp_haltsWithin (hT : N.tm.HaltsWithin x T) :
    (amp N r dec).tm.HaltsWithin x (T + (r * (T + x.length + 2) + 1)) := by
  intro w hw
  rw [init_eq_emb]
  exact run_halts hT 0 fresh_init (rewind_halts hT r 0 (by simp)) w hw

/-- **The runs are independent**: if `N` halts on `x` within `T`, the output of `amp N r dec`
is `[v]` with the probability that `dec` of the number of accepting blocks among `r + 1`
independent blocks of `T` coins is `v`. [AB09, §7.7, p. 139] -/
theorem amp_outputProb (hT : N.tm.HaltsWithin x T) (v : Bool) :
    (amp N r dec).outputProb x (T + (r * (T + x.length + 2) + 1)) [v] =
      randProb ((r + 1) * T) (fun l => dec (blockCount T (r + 1) (acc N x) l) = v) := by
  unfold FinNDTM.outputProb FinNDTM.outputWith
  rw [init_eq_emb, run_prob hT v (by simp) (by simp) fresh_init (rewind_halts hT r 0 (by simp))
    (rewind_prob hT v r 0 (by simp))]
  simp [val]

/-- **Majority of `2n + 1` independent blocks**: if `N` outputs `[v]` on `x` with probability at
least `1/2 + ε` over `T` coins, then the majority of `2n + 1` blocks is `v` with probability at
least `1 - 2 (1 - 4ε²)^n`. [AB09, §7.4.1]

**Proof sketch.** The majority errs only if at least half of the blocks err
(`blockCount_add_not`), and each block errs with probability at most `1/2 - ε` (for `v = false`,
outputs `[true]` and `[false]` are disjoint), so the Chernoff-type bound `randProb_tail_le`
applies. -/
theorem majority_randProb_ge {T n : ℕ} {ε : ℚ} (hε : 0 ≤ ε) (v : Bool)
    (hp : 1/2 + ε ≤ N.outputProb x T [v]) :
    1 - 2 * (1 - 4 * ε ^ 2) ^ n ≤ randProb ((2 * n + 1) * T)
      (fun l => decide (2 * n + 1 < 2 * blockCount T (2 * n + 1) (acc N x) l) = v) := by
  classical
  have tail : ∀ B : List Bool → Bool, randProb T (fun l => B l = true) ≤ 1/2 - ε →
      randProb ((2 * n + 1) * T) (fun l => 2 * n + 1 ≤ 2 * blockCount T (2 * n + 1) B l) ≤
        2 * (1 - 4 * ε ^ 2) ^ n := by
    intro B hB
    have := randProb_tail_le T (2 * n + 1) B hε hB
    rwa [show (2 * n + 1) / 2 = n by omega] at this
  have hpt : randProb T (fun l => acc N x l = true) = N.outputProb x T [true] :=
    randProb_congr fun r => by simp [acc, FinNDTM.outputWith]
  have hnot := randProb_not (m := (2 * n + 1) * T)
    (fun l => decide (2 * n + 1 < 2 * blockCount T (2 * n + 1) (acc N x) l) = v)
  cases v
  · have hsum : N.outputProb x T [true] + N.outputProb x T [false] ≤ 1 := by
      unfold FinNDTM.outputProb
      rw [← randProb_or_disjoint _ _ fun r h => by
        have := h.1.symm.trans h.2
        simp at this]
      exact randProb_le_one
    have hB : randProb T (fun l => acc N x l = true) ≤ 1/2 - ε := by
      rw [hpt]
      linarith
    have hmono : randProb ((2 * n + 1) * T)
        (fun l => ¬ decide (2 * n + 1 < 2 * blockCount T (2 * n + 1) (acc N x) l) = false) ≤
        randProb ((2 * n + 1) * T)
          (fun l => 2 * n + 1 ≤ 2 * blockCount T (2 * n + 1) (acc N x) l) :=
      randProb_mono fun r hr => by
        simp only [decide_eq_false_iff_not, not_not] at hr
        omega
    linarith [tail _ hB]
  · have hB : randProb T (fun l => (fun l => !acc N x l) l = true) ≤ 1/2 - ε := by
      have e : randProb T (fun l => (fun l => !acc N x l) l = true) =
          randProb T (fun l => acc N x l = false) := randProb_congr fun r => by simp
      rw [e, randProb_bool_false, hpt]
      linarith
    have hmono : randProb ((2 * n + 1) * T)
        (fun l => ¬ decide (2 * n + 1 < 2 * blockCount T (2 * n + 1) (acc N x) l) = true) ≤
        randProb ((2 * n + 1) * T) (fun l => 2 * n + 1 ≤
          2 * blockCount T (2 * n + 1) (fun l => !acc N x l) l) :=
      randProb_mono fun r hr => by
        have := blockCount_add_not T (2 * n + 1) (acc N x) (List.ofFn r)
        simp only [decide_eq_true_eq, not_lt] at hr
        omega
    linarith [tail _ hB]

/-! ### Space -/

/-- A work head of a run from the start lies within the number of cells the run visits.

**Proof sketch.** The head positions along the prefixes of `w` start at `0` and move by at most one
per step (`workTapePos_apply_le`), so the final position is below the number of positions visited
(`abs_lt_card_image_of_unitSteps`), which is one summand of `NDTM.spaceUsedWith`. -/
theorem abs_workTapePos_le {K : ℕ} {St : Type} (tm : NDTM K Bool St) (w : List Bool) {S : ℕ}
    (hs : tm.spaceUsedWith w (tm.initCfg x) ≤ S) (i : Fin K) :
    |(tm.runWith w (tm.initCfg x)).workTapePos i| ≤ S := by
  set p : ℕ → ℤ := fun j => (tm.runWith (w.take j) (tm.initCfg x)).workTapePos i with hp
  have hstep : ∀ j, |p (j + 1) - p j| ≤ 1 := by
    intro j
    by_cases hj : j < w.length
    · simp only [hp]
      rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, NDTM.runWith_append,
        NDTM.runWith_cons, NDTM.runWith_nil]
      unfold NDTM.stepWith
      split
      · simp
      · exact workTapePos_apply_le _ _ i
    · simp only [hp]
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp
  have hmem : (tm.runWith w (tm.initCfg x)).workTapePos i ∈
      (Finset.range (w.length + 1)).image p :=
    Finset.mem_image.mpr ⟨w.length, Finset.mem_range.mpr (Nat.lt_succ_self _), by
      simp [hp, List.take_length]⟩
  have hlt := MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps p (by simp [hp]) hstep
    w.length hmem
  have hcard : ((Finset.range (w.length + 1)).image p).card ≤
      tm.spaceUsedWith w (tm.initCfg x) :=
    Finset.single_le_sum (f := fun i => (tm.visitedWith w (tm.initCfg x) i).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Every work head of `C` lies within `S` of the origin. -/
def Good (S : ℕ) (C : ACfg N r x) : Prop := ∀ t, |C.workTapePos t| ≤ S

/-- Simulating a run of `N` keeps the heads within `S` if `N`'s branches use at most `S`
cells. -/
theorem good_emb {S : ℕ} (hN : ∀ w, N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ S)
    {D : ACfg N r x} (hD : Good S D) (j : Fin (r + 1)) (c : Fin (r + 2)) (u : List Bool) :
    Good S (emb D j c (N.tm.runWith u (N.tm.initCfg x))) := by
  intro t
  simp only [emb]
  split_ifs
  · exact abs_workTapePos_le N.tm u (hN u) _
  · exact hD t

/-- From a good rewinding configuration every run stays good.

**Proof sketch.** Induction on `i`, along `rewind_halts`. Rewinding and the final step move no work
head (`rewind_run`, `rewind_last`). After the restart, block `j + 1` follows a run of `N`, whose
heads stay within `S` (`good_emb`, from `abs_workTapePos_le`), and the other blocks are frozen;
`reach_comp` combines this with the induction hypothesis after the run. -/
theorem rewind_good {S : ℕ} (hN : ∀ w, N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ S) :
    ∀ (i : ℕ) (j : Fin (r + 1)), j.val + i = r → ∀ (c : Fin (r + 2)) (C : ACfg N r x),
      RewindAt C j c → Good S C → ∀ w, Good S ((amp N r dec).tm.runWith w C) := by
  intro i
  induction i with
  | zero =>
    intro j hj c C hC hg w
    have hlast : ¬ j.val < r := by omega
    match w with
    | [] => exact hg
    | true :: w' => rw [(rewind_last hC.1 hlast w').1]; exact hg
    | false :: w' => rw [(rewind_last hC.1 hlast w').2]; exact hg
  | succ i ih =>
    intro j hj c C hC hg w
    have hjr : j.val < r := by omega
    obtain ⟨p, -, hpos, hrun⟩ := rewind_run (dec := dec) hC.1 hjr
    by_cases hw : w.length ≤ p + 2
    · intro t
      rw [hpos w hw]
      exact hg t
    · have hE := restart_eq_emb C ⟨j.val + 1, by omega⟩ c
        (fun t ht => hC.2.2 t (by rw [ht]; exact Nat.lt_succ_self _)) hC.2.1
      have hF : Fresh (restart C ⟨j.val + 1, by omega⟩ c) (j.val + 1) :=
        fun t ht => hC.2.2 t (by omega)
      have hgE : Good S (restart C ⟨j.val + 1, by omega⟩ c) := hg
      rw [← List.take_append_drop (p + 2) w, NDTM.runWith_append,
        hrun _ (List.length_take_of_le (by omega)), hE]
      exact reach_comp (fun u b hu => step_emb _ _ c u b hu) (Good S) _ (N.tm.initCfg x)
        (fun u => good_emb hN hgE _ c u)
        (fun u hu w' => ih (⟨j.val + 1, by omega⟩ : Fin (r + 1))
          (by show j.val + 1 + i = r; omega) _ _ (rewindAt_emb c hu hF)
          (good_emb hN hgE _ c u) w')

/-- **The space of the repeated machine**: if every branch of `N` uses at most `s(|x|)`
cells, every branch of `amp N r dec` uses at most `(r + 1) k (2 s(|x|) + 1)` cells.

**Proof sketch.** Every head stays within `[-S, S]`, `S = s(|x|)`, along every run from the start
(`reach_comp` from `init_eq_emb`, then `rewind_good`); so each of the `(r + 1) k` tapes visits at
most `2S + 1` cells (`spaceUsedWith_le_of_ranges`). -/
theorem amp_usesSpace {s : ℕ → ℕ}
    (hN : ∀ x w : List Bool, N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s x.length)
    (x w : List Bool) :
    (amp N r dec).tm.spaceUsedWith w ((amp N r dec).tm.initCfg x) ≤
      (r + 1) * N.k * (2 * s x.length + 1) := by
  have hg0 : Good (s x.length) ((amp N r dec).tm.initCfg x) := fun t => by simp
  have hgood : ∀ u,
      Good (s x.length) ((amp N r dec).tm.runWith u ((amp N r dec).tm.initCfg x)) := by
    intro u
    rw [init_eq_emb]
    exact reach_comp (fun v b hv => step_emb _ 0 0 v b hv) (Good (s x.length)) u
      (N.tm.initCfg x) (fun v => good_emb (hN x) hg0 0 0 v)
      (fun v hv w' => rewind_good (hN x) r 0 (by simp) _ _ (rewindAt_emb 0 hv fresh_init)
        (good_emb (hN x) hg0 0 0 v) w')
  refine (spaceUsedWith_le_of_ranges (amp N r dec).tm w _ (fun _ => -(s x.length : ℤ))
    (fun _ => s x.length) fun u _ t => abs_le.mp (hgood u t)).trans (le_of_eq ?_)
  have h2 : ((s x.length : ℤ) - -(s x.length : ℤ) + 1).toNat = 2 * s x.length + 1 := by omega
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

end Randomized.Amplify
