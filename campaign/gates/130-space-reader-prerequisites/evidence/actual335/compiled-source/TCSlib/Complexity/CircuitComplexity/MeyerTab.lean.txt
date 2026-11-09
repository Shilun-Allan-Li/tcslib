/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerMachineWalk
import TCSlib.Complexity.ClassNP.EXP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the tableau language is in EXP

The specification of the tableau machine `Complexity.Meyer.tabTM M` and the membership
of its language in `EXP`: [AB09, proof of Thm 6.20], the step "the language of
snapshot bits of an exponential-time machine is in `EXP`", here for the head-relative
tableau (see `Meyer.lean`).

## Main definitions

* `Complexity.Meyer.tabAns` — the selected bit of a configuration of `M`.
* `Complexity.Meyer.tabFun` — the answer to a query string (`false` if truncated).
* `Complexity.Meyer.Tab` — the tableau language `{y | tabFun M y}`.

## Main results

* `Complexity.Meyer.tabTM_computes` — `tabTM M` computes `tabFun M` within
  `10 (n + 1) 2ⁿ` steps.
* `Complexity.Meyer.Tab_mem_EXP` — `Tab M ∈ EXP`.
* `Complexity.Meyer.tabFun_query` — on a well-formed query the answer is the selected
  bit of `M`'s configuration at time `val t`, walked `val a` cells.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115; Claim 2.4.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

variable (M : FinTM Bool)

/-- **The selected bit of a configuration** `c` of `M`, the selected head walked `a`
times (`Complexity.Meyer.wstep`). -/
def tabAns {x : List Bool} (sel : Sel M) (c : Cfg M.k Bool M.State x) (a : ℕ) : Bool :=
  selAnswer sel c.state (OutReg.ofList c.output) ((wstep M sel)^[a] c).inputSymbol
    ((wstep M sel)^[a] c).workTapeSymbols

/-- **The answer to a query string**: for a query `(bits, t, a, x)`, the selected bit of
the configuration of `M` on `x` after `val t` steps, walked `val a` cells; `false` on a
truncated string. -/
noncomputable def tabFun (y : List Bool) : Bool :=
  match parseQ (nbits M) y with
  | none => false
  | some (bits, t, a, x) =>
    tabAns M (decodeSel bits) (M.tm.runFrom (M.tm.initCfg x) (ctrVal t)) (ctrVal a)

/-- **The tableau language** of `M`. -/
def Tab : Language Bool := {y | tabFun M y = true}

/-- A word's value is below `2^length`. -/
theorem ctrVal_lt (w : List Bool) : ctrVal w < 2 ^ w.length := by
  induction w with
  | nil => simp [ctrVal]
  | cons b w ih => cases b <;> simp [ctrVal, pow_succ] <;> omega

/-- A parsed query's fields fit in the query.

**Proof sketch.** A parsed query is the selector bits, the two coded fields (twice their
lengths) with end pairs, and the rest (`readField_eq_some`). -/
theorem parseQ_length {y : List Bool} {bits : Fin (nbits M) → Bool} {t a x : List Bool}
    (h : parseQ (nbits M) y = some (bits, t, a, x)) :
    t.length ≤ y.length ∧ a.length ≤ y.length := by
  by_cases hlen : nbits M ≤ y.length
  · simp only [parseQ, if_pos hlen] at h
    cases h1 : readField (y.drop (nbits M)) with
    | none => rw [h1] at h; simp at h
    | some tr =>
      obtain ⟨t', r⟩ := tr
      rw [h1] at h
      simp only at h
      cases h2 : readField r with
      | none => rw [h2] at h; simp at h
      | some ax =>
        obtain ⟨a', x'⟩ := ax
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl, rfl⟩ := h
        obtain ⟨e, he⟩ := readField_eq_some h1
        obtain ⟨e', he'⟩ := readField_eq_some h2
        have := congrArg List.length he
        have h' := congrArg List.length he'
        simp at this h'
        omega
  · simp [parseQ, hlen] at h

/-- The loop entry is the loop configuration of `M`'s initial configuration. -/
theorem init_tag (x : List Bool) : VirtualTag (M.tm.initCfg x).inputPos true :=
  ⟨by simp, fun _ => rfl⟩

/-- **The specification of the tableau machine**: it computes `tabFun M` within
`10 (n + 1) 2ⁿ` steps on inputs of length `n`.

**Proof sketch.** Truncated queries are rejected within `n + 1` steps
(`tabTM_setup`). Otherwise the setup (`≤ 2n + 4` steps) reaches the simulation loop,
which runs `M` for `val t` steps (`loop_run`, `≤ (val t + 1)(2|t| + 3)` steps), and the
walk loop emits the answer (`walk_run`, `≤ (val a + 1)(2|a| + 3)` steps); with
`val w < 2^|w|` and `|t|, |a| ≤ n` the total is at most `10 (n + 1) 2ⁿ`. -/
theorem tabTM_computes :
    (tabTM M).ComputesFunInTime (fun y => [tabFun M y]) (fun n => 10 * (n + 1) * 2 ^ n) := by
  intro y
  have hN : 1 ≤ 2 ^ y.length := Nat.one_le_two_pow
  obtain ⟨hrej, hacc⟩ := tabTM_setup M y
  cases hp : parseQ (nbits M) y with
  | none =>
    obtain ⟨s, hs, h⟩ := hrej hp
    refine ((computesInTime_iff _ _ _ _).mpr ⟨h.1, ?_⟩).mono ?_
    · rw [h.2]; simp [tabFun, hp]
    calc s ≤ y.length + 1 := hs
      _ ≤ 10 * (y.length + 1) * 2 ^ y.length := by nlinarith
  | some q =>
    obtain ⟨bits, t, a, x⟩ := q
    obtain ⟨s₁, hs₁, h₁⟩ := hacc bits t a x hp
    obtain ⟨ht, ha⟩ := parseQ_length M hp
    rw [acfg_eq_lcfg] at h₁
    obtain ⟨s₂, hs₂, τC, zC, b', hb', h₂⟩ := loop_run M bits (fpos y (y.length + 1))
      (bufferTape a) 0 (ctrVal t) t (M.tm.initCfg x) M.tm.q₀ true rfl rfl (init_tag M x)
    set c' := M.tm.runFrom (M.tm.initCfg x) (ctrVal t) with hc'
    obtain ⟨s₃, hs₃, h₃⟩ := walk_run M bits (fpos y (y.length + 1)) c'.state
      (OutReg.ofList c'.output) τC zC (ctrVal a) a c' b' rfl hb'
    have hrun : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (s₁ + s₂ + s₃) =
        (tabTM M).tm.runFrom (lcfg M (.wdec bits c'.state (OutReg.ofList c'.output) b')
          (fpos y (y.length + 1)) c' τC zC (bufferTape a) 0) s₃ := by
      rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, h₁]
      simp only [Cfg.init, MultiTapeTM.initCfg] at h₂ ⊢
      rw [show OutReg.empty = OutReg.ofList ([] : List Bool) from rfl, h₂]
    refine ((computesInTime_iff _ _ _ _).mpr ⟨by rw [hrun]; exact h₃.1, ?_⟩).mono ?_
    · rw [hrun, h₃.2]
      simp [tabFun, hp, tabAns, c']
    · have hvt := ctrVal_lt t
      have hva := ctrVal_lt a
      have h2t : 2 ^ t.length ≤ 2 ^ y.length := Nat.pow_le_pow_right (by omega) ht
      have h2a : 2 ^ a.length ≤ 2 ^ y.length := Nat.pow_le_pow_right (by omega) ha
      have e2 : s₂ ≤ 2 ^ y.length * (2 * y.length + 3) :=
        hs₂.trans (Nat.mul_le_mul (by omega) (by omega))
      have e3 : s₃ ≤ 2 ^ y.length * (2 * y.length + 3) :=
        hs₃.trans (Nat.mul_le_mul (by omega) (by omega))
      have e1 : s₁ ≤ 2 ^ y.length * (2 * y.length + 4) :=
        hs₁.trans (Nat.le_mul_of_pos_left _ (by omega))
      nlinarith

/-- **The tableau language is in `EXP`** [AB09, proof of Thm 6.20: the snapshot language
of a `2^{p(n)}`-time machine is decidable in exponential time].

Here the language is decided in time `10 (n + 1) 2ⁿ ≤ 20 · 2^{n²}`, so it lies in
`DTIME(2^{n²}) ⊆ EXP`.

**Proof sketch.** `tabTM_computes`, with `(n + 1) 2ⁿ ≤ 2^{2n} ≤ 2 · 2^{n²}`. -/
theorem Tab_mem_EXP : Tab M ∈ EXP := by
  refine Set.mem_iUnion.mpr ⟨2, 20, tabTM M, fun y => ?_⟩
  have h := tabTM_computes M y
  have hind : MultiTapeTM.indicator (Tab M) y = tabFun M y := by
    simp only [MultiTapeTM.indicator, Tab, Set.mem_setOf_eq]
    by_cases hb : tabFun M y = true <;> simp [hb]
  rw [hind]
  refine h.mono ?_
  have h1 : y.length + 1 ≤ 2 ^ y.length := Nat.lt_two_pow_self
  have h2 : 2 * y.length ≤ y.length ^ 2 + 1 := by
    rcases Nat.lt_or_ge y.length 2 with h | h
    · interval_cases y.length <;> simp
    · nlinarith
  have h3 : 2 ^ (2 * y.length) ≤ 2 ^ (y.length ^ 2 + 1) := Nat.pow_le_pow_right (by omega) h2
  calc 10 * (y.length + 1) * 2 ^ y.length ≤ 10 * (2 ^ y.length * 2 ^ y.length) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
    _ = 10 * 2 ^ (2 * y.length) := by rw [← pow_add, two_mul]
    _ ≤ 10 * 2 ^ (y.length ^ 2 + 1) := Nat.mul_le_mul_left _ h3
    _ = 20 * 2 ^ y.length ^ 2 := by rw [pow_succ]; ring

end Complexity.Meyer
