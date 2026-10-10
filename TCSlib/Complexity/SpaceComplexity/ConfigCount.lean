/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configuration counting: space-bounded machines halt quickly, `L ⊆ P`

[AB09, §4.1.1 and Thm 4.2]: a deterministic machine that halts never repeats a
configuration, and a machine using `s` work cells has at most `2^{O(s)} · poly(n)`
configurations, so it halts within that many steps. For `s = O(log n)` this is a
polynomial, giving `L ⊆ P` and "logspace computations run in polynomial time" [AB09, p. 112].

## Main definitions

* `Turing.FinTM.configBound` — the configuration count
  `(|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s + 1)^k` of a `k`-tape machine with state set `Q`
  on inputs of length `n` with at most `s` visited work cells.

## Main results

* `Turing.MultiTapeTM.abs_pos_lt_card_visited` — the visited cells of a tape form an
  interval around the origin, so every visited position `z` has `|z| < #visited`.
* `Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps`,
  `Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none` — their run-generic forms,
  shared with nondeterministic runs (added 2026-10-10).
* `Turing.FinTM.ComputesInTime.of_spaceUsed_le` — a computation that has halted by time `t`
  having visited at most `s` cells has in fact halted by time `configBound M |x| s`.
  [AB09, §4.1.1, the deterministic case of Thm 4.2]
* `Complexity.LOGSPACE_subset_P` — `L ⊆ P`. [AB09, Thm 4.2 for `S = log n`]
* `Complexity.polyTimeComputable_of_computesInSpace` — a function computed in logarithmic
  space is polynomial-time computable. [AB09, p. 112: "logspace computations run in
  polynomial time"]

## Design

A configuration of the vendored model also records the output tape, which grows; the
argument is run on the *core* `(state, input position, work tapes, work heads)`, whose
evolution does not depend on the output. If two times before the first halting time have
the same core, the core sequence is periodic from then on and the machine never halts.
Cores reached with at most `s` visited cells are coded injectively into a finite type:
heads lie in `[-s, s]` (the visited set is an interval containing `0`, by a discrete
intermediate value argument) and every nonblank cell has been visited.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4 and Theorem 4.2; §6.2.1, p. 112.)
-/

namespace Turing

namespace MultiTapeTM

variable {k : ℕ} {S : Type} {x : List Bool}

/-! ### Internal helpers: cores of configurations -/

namespace ConfigCount

/-- The core of a configuration: everything but the output tape. -/
def core (c : Cfg k Bool S x) :
    Option S × Fin (x.length + 2) × (Fin k → ℤ → Option Bool) × (Fin k → ℤ) :=
  (c.state, c.inputPos, c.workTapes, c.workTapePos)

/-- The core after a step depends only on the core before it. -/
lemma core_step (tm : MultiTapeTM k Bool S) {c d : Cfg k Bool S x} (h : core c = core d) :
    core (tm.step c) = core (tm.step d) := by
  simp only [core, Prod.mk.injEq] at h
  obtain ⟨hs, hi, hw, hp⟩ := h
  have hsym : c.inputSymbol = d.inputSymbol := by
    unfold Cfg.inputSymbol; simp only [hi]
  have hws : c.workTapeSymbols = d.workTapeSymbols := by
    funext i; simp only [Cfg.workTapeSymbols, hw, hp]
  unfold step
  rw [hs]
  cases d.state with
  | none => simp [core, hs, hi, hw, hp]
  | some q =>
    simp only [core, Action.apply, hsym, hws, hi, hw, hp]

/-- Equal cores stay equal along runs. -/
lemma core_runFrom (tm : MultiTapeTM k Bool S) {c d : Cfg k Bool S x} (h : core c = core d)
    (t : ℕ) : core (tm.runFrom c t) = core (tm.runFrom d t) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step']
    exact core_step tm ih

/-- Before the first halting time, no core repeats.

**Proof sketch.** If the cores at times `t₁ < t₂` agree, then the cores at `t₁ + j` and
`t₂ + j` agree for every `j`, so the core at `t₁ + r` equals the core at `t₁ + (r mod p)`
with `p = t₂ - t₁`. At the first halting time `T = t₁ + r` the state is `none`, but
`t₁ + (r mod p) < t₂ < T` is an earlier, non-halted time. -/
lemma core_injOn (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (T : ℕ)
    (hT : (tm.runFrom c T).state = none)
    (hmin : ∀ t < T, (tm.runFrom c t).state ≠ none) {t₁ t₂ : ℕ} (h₁₂ : t₁ < t₂)
    (h₂ : t₂ < T) : core (tm.runFrom c t₁) ≠ core (tm.runFrom c t₂) := by
  intro heq
  set p := t₂ - t₁ with hp
  have hpos : 0 < p := by omega
  -- the core at `t₁ + r` equals the one at `t₁ + (r - p)` once `r ≥ p`
  have hback : ∀ r, p ≤ r →
      core (tm.runFrom c (t₁ + r)) = core (tm.runFrom c (t₁ + (r - p))) := by
    intro r hr
    have e1 : t₁ + r = t₂ + (r - p) := by omega
    rw [e1, runFrom_add, runFrom_add c t₁]
    exact core_runFrom tm heq.symm _
  have hmod : ∀ r, core (tm.runFrom c (t₁ + r)) = core (tm.runFrom c (t₁ + r % p)) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      by_cases hr : r < p
      · rw [Nat.mod_eq_of_lt hr]
      · rw [hback r (by omega), ih (r - p) (by omega), ← Nat.mod_eq_sub_mod (by omega)]
  have hTgt : t₂ < T := h₂
  have hr := hmod (T - t₁)
  rw [show t₁ + (T - t₁) = T by omega] at hr
  have hlt : t₁ + (T - t₁) % p < T := by
    have := Nat.mod_lt (T - t₁) hpos
    omega
  apply hmin _ hlt
  have := congrArg Prod.fst hr
  simp only [core] at this
  rw [← this, hT]

/-- Discrete intermediate values: a sequence of integers starting at `0` and moving by at
most one per step passes through every integer between `0` and any of its values.

**Proof sketch.** Induction on `t`. If `y` lies between `0` and `p t`, the induction hypothesis
applies. Otherwise `y` lies between `p t` and `p (t + 1)`, which differ by at most one, so `y =
p (t + 1)`. -/
lemma exists_eq_of_between (p : ℕ → ℤ) (h0 : p 0 = 0) (hstep : ∀ j, |p (j + 1) - p j| ≤ 1) :
    ∀ t (y : ℤ), (0 ≤ y ∧ y ≤ p t ∨ p t ≤ y ∧ y ≤ 0) → ∃ j ≤ t, p j = y := by
  intro t
  induction t with
  | zero =>
    intro y hy
    exact ⟨0, le_rfl, by rw [h0] at hy; omega⟩
  | succ t ih =>
    intro y hy
    have hs := hstep t
    rw [abs_le] at hs
    by_cases hin : 0 ≤ y ∧ y ≤ p t ∨ p t ≤ y ∧ y ≤ 0
    · obtain ⟨j, hj, hpj⟩ := ih y hin
      exact ⟨j, by omega, hpj⟩
    · exact ⟨t + 1, le_rfl, by omega⟩

/-- An integer sequence starting at `0` and moving by at most one per step: every attained
value `z` up to time `t` satisfies `|z| < #(values attained up to t)`. The run-generic form
of `Turing.MultiTapeTM.abs_pos_lt_card_visited`, shared with nondeterministic runs (added
2026-10-10).

**Proof sketch.** The attained set contains the `|z| + 1` integers between `0` and `z`, by the
discrete intermediate value theorem `exists_eq_of_between`; compare cardinalities
(`Int.card_Icc`). -/
lemma abs_lt_card_image_of_unitSteps (p : ℕ → ℤ) (h0 : p 0 = 0)
    (hstep : ∀ j, |p (j + 1) - p j| ≤ 1) (t : ℕ) {z : ℤ}
    (hz : z ∈ (Finset.range (t + 1)).image p) :
    |z| < ((Finset.range (t + 1)).image p).card := by
  obtain ⟨t', ht', hzt⟩ : ∃ t' ≤ t, p t' = z := by
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t', ht', h⟩ := hz
    exact ⟨t', by omega, h⟩
  have hsub : Finset.Icc (min 0 z) (max 0 z) ⊆ (Finset.range (t + 1)).image p := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    obtain ⟨j, hj, hpj⟩ := exists_eq_of_between p h0 hstep t' y (by
      rw [hzt]; rcases le_total 0 z with h | h
      · left; simp only [min_eq_left h, max_eq_right h] at hy; omega
      · right; simp only [min_eq_right h, max_eq_left h] at hy; omega)
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨j, by omega, hpj⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  rcases le_total 0 z with h | h
  · simp only [min_eq_left h, max_eq_right h] at hc
    rw [abs_of_nonneg h]; omega
  · simp only [min_eq_right h, max_eq_left h] at hc
    rw [abs_of_nonpos h]; omega

/-- Along any sequence of configurations from blank work tapes in which each step is the
identity or one applied action, a cell that is nonblank at time `t` was under its head at
some time `≤ t`. The run-generic form of `Turing.MultiTapeTM.mem_visited_of_ne_none`, shared
with nondeterministic runs (added 2026-10-10).

**Proof sketch.** Induction on `t`. Initially every cell is blank. An applied action writes
only the cell under the head, which is visited at that step; other cells keep their
contents. -/
lemma mem_image_workTapePos_of_ne_none {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (cs : ℕ → Cfg k Symbol State input) (h0 : ∀ i z, (cs 0).workTapes i z = none)
    (hstep : ∀ j, cs (j + 1) = cs j ∨ ∃ a : Action k Symbol State, cs (j + 1) = a.apply (cs j))
    (t : ℕ) (i : Fin k) (z : ℤ) (hz : (cs t).workTapes i z ≠ none) :
    z ∈ (Finset.range (t + 1)).image fun j => (cs j).workTapePos i := by
  induction t with
  | zero => exact absurd (h0 i z) hz
  | succ t ih =>
    simp only [Finset.mem_image, Finset.mem_range] at ih ⊢
    rcases hstep t with h | ⟨a, h⟩
    · rw [h] at hz
      obtain ⟨j, hj, hj'⟩ := ih hz
      exact ⟨j, by omega, hj'⟩
    · rw [h] at hz
      dsimp only [Action.apply] at hz
      cases hw : (a.workTapes i).1 with
      | none =>
        rw [hw] at hz
        obtain ⟨j, hj, hj'⟩ := ih hz
        exact ⟨j, by omega, hj'⟩
      | some s =>
        rw [hw] at hz
        dsimp only at hz
        by_cases hzp : z = (cs t).workTapePos i
        · exact ⟨t, by omega, hzp.symm⟩
        · rw [Function.update_of_ne hzp] at hz
          obtain ⟨j, hj, hj'⟩ := ih hz
          exact ⟨j, by omega, hj'⟩

end ConfigCount

open ConfigCount

/-- The positions visited by work head `i` from an initial configuration form a set in
which every position `z` satisfies `|z| < #visited`: the visited set contains the whole
interval between `0` and `z`.

**Proof sketch.** The visited set contains `0` (the start) and, by the discrete intermediate
value theorem (`exists_eq_of_between`, the head moves by at most one cell per step), every
integer between `0` and any visited `z`. So it contains the `|z| + 1` integers between `0` and
`z`, and its cardinality exceeds `|z|`. (Since 2026-10-10 this is an instance of the
run-generic `ConfigCount.abs_lt_card_image_of_unitSteps`.) -/
lemma abs_pos_lt_card_visited (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (i : Fin k) {z : ℤ} (hz : z ∈ tm.visitedByTapeHead (tm.initCfg x) t i) :
    |z| < (tm.visitedByTapeHead (tm.initCfg x) t i).card :=
  abs_lt_card_image_of_unitSteps (fun j => (tm.runFrom (tm.initCfg x) j).workTapePos i)
    (by simp)
    (fun j => by
      simp only [runFrom_succ_eq_step']
      exact tm.workTapePos_step_le _ i) t hz

/-- A cell holding a nonblank symbol at time `t` was visited by its head before time `t`.

**Proof sketch.** Induction on `t`. Initially every work cell is blank. A step writes only the
cell under the head, which is visited at that step; other cells keep their contents and stay
visited by monotonicity of the visited sets. (Since 2026-10-10 this is an instance of the
run-generic `ConfigCount.mem_image_workTapePos_of_ne_none`.) -/
lemma mem_visited_of_ne_none (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (i : Fin k) (z : ℤ) (hz : (tm.runFrom (tm.initCfg x) t).workTapes i z ≠ none) :
    z ∈ tm.visitedByTapeHead (tm.initCfg x) t i :=
  mem_image_workTapePos_of_ne_none (fun j => tm.runFrom (tm.initCfg x) j)
    (by simp [initCfg, Cfg.init])
    (fun j => by
      simp only [runFrom_succ_eq_step']
      unfold step
      cases (tm.runFrom (tm.initCfg x) j).state with
      | none => exact Or.inl rfl
      | some q => exact Or.inr ⟨_, rfl⟩) t i z hz

/-- Visited sets grow with time. -/
lemma visitedByTapeHead_mono (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) {t t' : ℕ}
    (h : t ≤ t') (i : Fin k) : tm.visitedByTapeHead c t i ⊆ tm.visitedByTapeHead c t' i := by
  intro z hz
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz ⊢
  obtain ⟨j, hj, h'⟩ := hz
  exact ⟨j, by omega, h'⟩

/-- Space used grows with time. -/
lemma spaceUsed_mono (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) {t t' : ℕ}
    (h : t ≤ t') : tm.spaceUsed c t ≤ tm.spaceUsed c t' :=
  Finset.sum_le_sum fun i _ => Finset.card_le_card (tm.visitedByTapeHead_mono c h i)

namespace ConfigCount

/-- The code of an integer in `[-B, B]` as an element of `Fin (2B + 1)`. -/
def posCode (B : ℕ) (z : ℤ) : Fin (2 * B + 1) :=
  ⟨min (z + B).toNat (2 * B), by omega⟩

/-- The position code is injective on positions of absolute value at most `B`. -/
lemma posCode_injOn (B : ℕ) {z z' : ℤ} (hz : |z| ≤ B) (hz' : |z'| ≤ B)
    (h : posCode B z = posCode B z') : z = z' := by
  simp only [posCode, Fin.mk.injEq] at h
  rw [abs_le] at hz hz'
  omega

/-- The finite code of a core with heads and nonblank cells in `[-B, B]`. -/
def coreCode (B : ℕ) (c : Cfg k Bool S x) :
    Option S × Fin (x.length + 2) × (Fin k → Fin (2 * B + 1) → Option Bool) ×
      (Fin k → Fin (2 * B + 1)) :=
  (c.state, c.inputPos, fun i j => c.workTapes i ((j : ℤ) - B),
    fun i => posCode B (c.workTapePos i))

/-- The code is injective on cores whose heads and nonblank cells lie in `[-B, B]`.

**Proof sketch.** State, input position and head positions are read off the code directly, the
positions by injectivity of `posCode` on `[-B, B]`. A cell `z` with `|z| ≤ B` is recorded in the
code. A cell with `|z| > B` is blank in both configurations by hypothesis. -/
lemma coreCode_inj (B : ℕ) {c d : Cfg k Bool S x}
    (hc : ∀ i, |c.workTapePos i| ≤ B ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ B)
    (hd : ∀ i, |d.workTapePos i| ≤ B ∧ ∀ z, d.workTapes i z ≠ none → |z| ≤ B)
    (h : coreCode B c = coreCode B d) : core c = core d := by
  simp only [coreCode, Prod.mk.injEq] at h
  obtain ⟨hs, hi, hw, hp⟩ := h
  simp only [core, Prod.mk.injEq]
  refine ⟨hs, hi, ?_, ?_⟩
  · funext i z
    by_cases hz : |z| ≤ B
    · have := congrFun (congrFun hw i) ⟨(z + B).toNat, by rw [abs_le] at hz; omega⟩
      simp only at this
      rwa [show (((z + B).toNat : ℕ) : ℤ) - B = z by rw [abs_le] at hz; omega] at this
    · have h1 : c.workTapes i z = none := by
        by_contra hne; exact hz ((hc i).2 z hne)
      have h2 : d.workTapes i z = none := by
        by_contra hne; exact hz ((hd i).2 z hne)
      rw [h1, h2]
  · funext i
    exact posCode_injOn B (hc i).1 (hd i).1 (congrFun hp i)

end ConfigCount

end MultiTapeTM

namespace FinTM

open MultiTapeTM MultiTapeTM.ConfigCount

/-- The number of codes of configurations of `M` on inputs of length `n` with heads and
nonblank cells in `[-s, s]`: `(|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s + 1)^k`. -/
def configBound (M : FinTM Bool) (n s : ℕ) : ℕ :=
  (Fintype.card M.State + 1) * (n + 2) * 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k

/-- **Space-bounded halting computations are short** [AB09, §4.1.1]: if `M` has halted on
`x` with output `w` by time `t`, having visited at most `s` work cells, then it has halted
with output `w` by time `configBound M |x| s`.

**Proof sketch.** Let `T ≤ t` be the first halting time. Up to time `t` every head lies in
`[-s, s]` (`abs_pos_lt_card_visited`: the visited cells of a tape form an interval around
`0`, of size at most the space used) and so does every nonblank cell
(`mem_visited_of_ne_none`). Hence the cores at times `< T` have pairwise distinct
(`core_injOn`) codes in a finite type of size `configBound M |x| s`, so `T` is at most
that size; the output is frozen after `T`. -/
theorem ComputesInTime.of_spaceUsed_le {M : FinTM Bool} {x w : List Bool} {t s : ℕ}
    (h : M.ComputesInTime x w t) (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s) :
    M.ComputesInTime x w (M.configBound x.length s) := by
  classical
  rw [computesInTime_iff] at h ⊢
  obtain ⟨hhalt, hout⟩ := h
  have hex : ∃ T, (M.tm.runFrom (M.tm.initCfg x) T).state = none := ⟨t, hhalt⟩
  set T := Nat.find hex with hTdef
  have hT : (M.tm.runFrom (M.tm.initCfg x) T).state = none := Nat.find_spec hex
  have hTt : T ≤ t := Nat.find_min' hex hhalt
  have hmin : ∀ t' < T, (M.tm.runFrom (M.tm.initCfg x) t').state ≠ none :=
    fun t' ht' => Nat.find_min hex ht'
  -- bounds on heads and nonblank cells up to time `t`
  have hbound : ∀ t' ≤ t, ∀ i, |(M.tm.runFrom (M.tm.initCfg x) t').workTapePos i| ≤ s ∧
      ∀ z, (M.tm.runFrom (M.tm.initCfg x) t').workTapes i z ≠ none → |z| ≤ s := by
    intro t' ht' i
    have hcard : (M.tm.visitedByTapeHead (M.tm.initCfg x) t i).card ≤ s :=
      (M.tm.spaceUsedByTape_le_spaceUsed _ t i).trans hs
    have hmem : ∀ z ∈ M.tm.visitedByTapeHead (M.tm.initCfg x) t i, |z| ≤ s := fun z hz =>
      ((M.tm.abs_pos_lt_card_visited x t i hz).trans_le (by exact_mod_cast hcard)).le
    refine ⟨hmem _ ?_, fun z hz => hmem z ?_⟩
    · simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range]
      exact ⟨t', by omega, rfl⟩
    · exact M.tm.visitedByTapeHead_mono _ ht' i (M.tm.mem_visited_of_ne_none x t' i z hz)
  -- injectivity of the code map on times before `T`
  have hinj : Set.InjOn (fun t' => coreCode s (M.tm.runFrom (M.tm.initCfg x) t'))
      (Finset.range T : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hc := coreCode_inj s (hbound a (by omega)) (hbound b (by omega)) hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact core_injOn M.tm _ T hT hmin h' hb hc
    · exact core_injOn M.tm _ T hT hmin h' ha hc.symm
  have hcardT : T ≤ M.configBound x.length s := by
    have := Finset.card_le_card_of_injOn _ (fun a _ => Finset.mem_univ _) hinj
    simp only [Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_option,
      Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Fintype.card_bool] at this
    rw [← pow_mul, Nat.mul_comm (2 * s + 1) M.k] at this
    refine this.trans (le_of_eq ?_)
    simp only [configBound]
    ring
  have hfin : M.tm.runFrom (M.tm.initCfg x) (M.configBound x.length s) =
      M.tm.runFrom (M.tm.initCfg x) T := by
    rw [show M.configBound x.length s = T + (M.configBound x.length s - T) by omega,
      runFrom_add, runFrom_of_halt _ hT]
  have hfin' : M.tm.runFrom (M.tm.initCfg x) t = M.tm.runFrom (M.tm.initCfg x) T := by
    rw [show t = T + (t - T) by omega, runFrom_add, runFrom_of_halt _ hT]
  rw [hfin]
  exact ⟨hT, by rw [← hfin']; exact hout⟩

/-- For a logarithmic space bound the configuration count is polynomial:
`configBound M n (c · logSpace n) ≤ A · (n + 1)^d` with `A = 2 (|Q| + 1) 2^{5kc + 3k}` and
`d = 5kc + 1`.

**Proof sketch.** Write `L = ⌊log₂ n⌋`, so `2^L ≤ n + 1`, and `s = c (L + 1)`. Bound
`3 ≤ 2²` and `2s + 1 ≤ 2^{s+1}`; the product `3^{k(2s+1)} (2s+1)^k` is then at most
`2^{5ks + 3k} = (2^L)^{5kc} · 2^{5kc + 3k}`, and `n + 2 ≤ 2 (n + 1)`. -/
theorem configBound_logSpace_le (M : FinTM Bool) (c n : ℕ) :
    M.configBound n (c * Complexity.logSpace n) ≤
      ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
        (n + 1) ^ (5 * M.k * c + 1) := by
  set L := Nat.log 2 n with hL
  set s := c * Complexity.logSpace n with hs
  have hsL : s = c * (L + 1) := rfl
  have h2L : 2 ^ L ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [hL, h]
    · exact (Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ n)
  have h3 : 3 ^ (M.k * (2 * s + 1)) ≤ 2 ^ (2 * (M.k * (2 * s + 1))) := by
    rw [pow_mul 2 2]; exact Nat.pow_le_pow_left (show 3 ≤ 2 ^ 2 by decide) _
  have hs2 : 2 * s + 1 ≤ 2 ^ (s + 1) := by
    have := s.lt_two_pow_self
    rw [pow_succ]; omega
  have h4 : (2 * s + 1) ^ M.k ≤ 2 ^ ((s + 1) * M.k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hs2 _
  have hexp : 2 * (M.k * (2 * s + 1)) + (s + 1) * M.k =
      L * (5 * M.k * c) + (5 * M.k * c + 3 * M.k) := by
    rw [hsL]; ring
  have hprod : 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k ≤
      (n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) := by
    calc 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k
        ≤ 2 ^ (2 * (M.k * (2 * s + 1))) * 2 ^ ((s + 1) * M.k) := Nat.mul_le_mul h3 h4
      _ = (2 ^ L) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) := by
        rw [← pow_add, hexp, pow_add, pow_mul]
      _ ≤ (n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2L _)
  calc M.configBound n s
      = (Fintype.card M.State + 1) * (n + 2) *
          (3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k) := by
        simp only [configBound]; ring
    _ ≤ (Fintype.card M.State + 1) * (2 * (n + 1)) *
          ((n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hprod
    _ = ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
          (n + 1) ^ (5 * M.k * c + 1) := by ring

/-- A computation in logarithmic space is a computation in polynomial time, by the same
machine: if `M` computes `f` in space `c · logSpace`, then `M` computes `f` within
`A · (n + 1)^d` steps. [AB09, p. 112: "logspace computations run in polynomial time"]

**Proof sketch.** `ComputesInTime.of_spaceUsed_le` bounds the halting time by the
configuration count, which `configBound_logSpace_le` bounds by a polynomial. -/
theorem ComputesInSpace.computesFunInTime {M : FinTM Bool} {f : List Bool → List Bool}
    {c : ℕ} (h : M.ComputesInSpace f fun n => c * Complexity.logSpace n) :
    M.ComputesFunInTime f fun n =>
      ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
        (n + 1) ^ (5 * M.k * c + 1) := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact (ht.of_spaceUsed_le hsp).mono (configBound_logSpace_le M c x.length)

end FinTM

end Turing

namespace Complexity

open Turing

/-- **`L ⊆ P`** [AB09, Thm 4.2 with `S(n) = log n`; p. 112]: a language decided in
logarithmic space is decided in polynomial time — by the same machine.

**Proof sketch.** `Turing.FinTM.ComputesInSpace.computesFunInTime` turns the logspace
decider into a decider within `A · (n + 1)^d` steps; conclude with `Complexity.mem_P_iff`. -/
theorem LOGSPACE_subset_P : LOGSPACE ⊆ P := by
  rintro L ⟨c, M, hM⟩
  rw [mem_P_iff]
  exact ⟨_, _, M, FinTM.ComputesInSpace.computesFunInTime hM⟩

/-- A function computed by a machine in logarithmic space is polynomial-time computable.
[AB09, p. 112] -/
theorem polyTimeComputable_of_computesInSpace {f : List Bool → List Bool} {M : FinTM Bool}
    {c : ℕ} (h : M.ComputesInSpace f fun n => c * logSpace n) : PolyTimeComputable f :=
  ⟨M, _, _, FinTM.ComputesInSpace.computesFunInTime h⟩

end Complexity
