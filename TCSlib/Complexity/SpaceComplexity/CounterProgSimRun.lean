/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.CounterProgSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counter programs on unary-logspace inputs are unary-logspace

The closure property behind the logspace half of [AB09, Remark 6.7]: if a counter program
(`Complexity.CounterProg`) halts within polynomially many steps on the words `u(n)`, and `u`
is unary-logspace (its bits and length are decidable in logarithmic space from `⟨1ⁿ, i⟩`),
then so is the sequence of its outputs. This is the composition of implicitly logspace
computable functions [AB09, Lemma 4.17] in the special form needed here: the second
function is a polynomial-time counter program, whose registers are therefore polynomially
bounded and fit in `O(log n)` bits.

## Main results

* `Complexity.CPSim.sim_run` — the simulating machine answers for the whole run.
* `Complexity.UnaryLogspace.counterProg` — the closure property.
* `Complexity.CounterProg.length_out_le` — the outputs have polynomial length.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17; §6.1.1, Remark 6.7.)
-/

namespace Complexity

namespace CPSim

open Turing LogProg

variable {R : ℕ} {Λ : Type} {P : Λ → CounterProg.Instr R Λ} {l₀ : Λ} {lm : Bool}

/-- The answer for an index inside a prefix is the prefix's answer. -/
lemma ans_append (O e : List Bool) {p : ℕ} (hp : p < O.length) :
    ans lm (O ++ e) p = ans lm O p := by
  cases lm
  · simp [ans, List.getD_eq_getElem?_getD, List.getElem?_append_left hp]
  · simp [ans]; omega

/-- Past the output the answer is `0`. -/
lemma ans_of_le (O : List Bool) {p : ℕ} (hp : O.length ≤ p) : ans lm O p = false := by
  cases lm
  · simp [ans, List.getD_eq_getElem?_getD, List.getElem?_eq_none hp]
  · simp [ans]; omega

/-- The counter state is within `B`. -/
def Bd (B : ℕ) (s : CounterProg.St R Λ) : Prop :=
  (∀ r, s.regs r ≤ B) ∧ s.pos ≤ B ∧ s.out.length ≤ B

section Run

variable {n p : ℕ} {u : List Bool} {o : Fin 2 → List Bool → Bool}
  (ho0 : ∀ h, o 0 (pairEncode (List.replicate n true) (Nat.bits h)) = decide (h < u.length))
  (ho1 : ∀ h, o 1 (pairEncode (List.replicate n true) (Nat.bits h)) = u.getD h false)
  {B : ℕ}

include ho0 ho1 in
/-- **The whole run.** From the configuration simulating a running counter state `s` with
`|out| ≤ p`, if `P` halts after `k` more steps, all states within `B`, the machine answers
`ans lm O p` for the final output `O`.

**Proof sketch.** Induction on `k`, one counter step at a time (`sim_step`): a halting step
answers `0` (the index is past the output); a step printing the `p`-th bit answers it, and
later steps only append (`CounterProg.run_out`, `ans_append`); otherwise continue. -/
lemma sim_run : ∀ (k : ℕ) (s : CounterProg.St R Λ) (tm : ℕ) (l : Λ), s.lbl = some l →
    s.out.length ≤ p → tm ≤ B → (CounterProg.run P u s k).lbl = none →
    (∀ j ≤ k, Bd B (CounterProg.run P u s j)) →
    AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
      (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
      (cf (.sim l) (ev s.regs s.pos s.out.length tm)) (ans lm (CounterProg.run P u s k).out p) := by
  intro k
  induction k with
  | zero =>
    intro s tm l hl _ _ hk _
    rw [CounterProg.run_zero, hl] at hk; exact absurd hk (by simp)
  | succ k ih =>
    intro s tm l hl hp htm hk hbd
    obtain ⟨lbl, ρ, ps, out⟩ := s
    simp only at hl; subst hl
    obtain ⟨hρ, hps, hout⟩ := hbd 0 (by omega)
    obtain ⟨hρ', hps', hout'⟩ := hbd 1 (by omega)
    rw [CounterProg.run_zero] at hρ hps hout
    rcases sim_step (P := P) (l₀ := l₀) (lm := lm) ho0 ho1 l ρ ps out tm hp hρ hps hout htm
      (CounterProg.step P u ⟨some l, ρ, ps, out⟩) rfl hρ' hps' hout' with
      ⟨hnone, hout1, hh⟩ | ⟨l', hl', (⟨hle, tm', htm', hr⟩ | ⟨hlt, hh⟩)⟩
    · rw [CounterProg.run_succ, CounterProg.run_of_halted _ _ _ hnone, hout1,
        ans_of_le _ hp]
      exact hh
    · rw [CounterProg.run_succ] at hk ⊢
      refine hr.halt (ih _ tm' l' hl' hle htm' hk fun j hj => ?_)
      have := hbd (j + 1) (by omega)
      rwa [CounterProg.run_succ] at this
    · rw [CounterProg.run_succ]
      obtain ⟨e, he⟩ := CounterProg.run_out P u (CounterProg.step P u ⟨some l, ρ, ps, out⟩) k
      rw [he, ans_append _ _ hlt]
      exact hh

end Run

end CPSim

namespace CounterProg

variable {R : ℕ} {Λ : Type}

/-- **Outputs of polynomially many steps have polynomial length**: `t ≤ C (n + 1)^c` steps
print at most `(C + 1)² (n + 1)^{2c}` bits. -/
theorem length_out_le (P : Λ → Instr R Λ) (l₀ : Λ) (x : List Bool) (C c n t : ℕ)
    (ht : t ≤ C * (n + 1) ^ c) :
    (run P x (init l₀) t).out.length ≤ (C + 1) ^ 2 * (n + 1) ^ (2 * c) := by
  have h := run_init_out_le P x l₀ t
  have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have e : (C + 1) ^ 2 * (n + 1) ^ (2 * c) = ((C + 1) * (n + 1) ^ c) ^ 2 := by ring
  rw [e]
  have : t + 1 ≤ (C + 1) * (n + 1) ^ c := by nlinarith
  nlinarith

end CounterProg

open Turing LogProg CPSim in
/-- **Counter programs preserve unary-logspace sequences** [AB09, Lemma 4.17, for a
polynomial-time counter program as the outer function]: if `u` is unary-logspace and the
counter program `P` halts on every `u(n)` within `C (n + 1)^c` steps with output `g(n)`, then
`g` is unary-logspace.

**Proof sketch.** For each of the two languages, `arm_decides_poly` with the simulating
machine `CPSim.A` (length or bit mode) and the deciders of `u`: on `⟨1ⁿ, bits p⟩` the
machine validates the input and runs `sim_run` from the initial state. Within `t ≤ N =
C (n + 1)^c` steps the registers are at most `N`, the input position at most `N`, the output
count at most `N (N + 1)` (`CounterProg.run_init_out_le`), so all registers are below
`(N + 1)² ≤ (C + 1)² (|y| + 1)^{2c}`. Malformed inputs are rejected at once. -/
theorem UnaryLogspace.counterProg {R : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (P : Λ → CounterProg.Instr R Λ) (l₀ : Λ) {u g : ℕ → List Bool} (hu : UnaryLogspace u)
    (C c : ℕ) (hrun : ∀ n, ∃ t ≤ C * (n + 1) ^ c,
      (CounterProg.run P (u n) (CounterProg.init l₀) t).lbl = none ∧
      (CounterProg.run P (u n) (CounterProg.init l₀) t).out = g n) :
    UnaryLogspace g := by
  let As : Fin 2 → Language Bool := fun j => if j = 0 then uLen u else uBit u
  have hAs : ∀ j, As j ∈ LOGSPACE := by
    intro j; fin_cases j
    · exact hu.2
    · exact hu.1
  have key : ∀ lm : Bool, (if lm then uLen g else uBit g) ∈ LOGSPACE := by
    intro lm
    refine arm_decides_poly (A P l₀ lm) .start As hAs ((C + 1) ^ 2) (2 * c) fun y => ?_
    by_cases hv : ValidPlain y
    · obtain ⟨n, w, rfl, hw⟩ := hv
      rw [canon_eq_bits w hw]
      set p := bitsVal w
      obtain ⟨t, ht, hhalt, hout⟩ := hrun n
      set N := C * (n + 1) ^ c with hN
      set B := (N + 1) ^ 2 with hB
      have ho0 : ∀ h, (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) 0
          (pairEncode (List.replicate n true) (Nat.bits h)) = decide (h < (u n).length) := by
        intro h
        simp only [As, ↓reduceIte, indicator_eq_decide]
        exact decide_eq_decide.mpr (mem_uLen u n h)
      have ho1 : ∀ h, (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) 1
          (pairEncode (List.replicate n true) (Nat.bits h)) = (u n).getD h false := by
        intro h
        show MultiTapeTM.indicator (uBit u : Set (List Bool)) _ = _
        have := mem_uBit u n h
        unfold MultiTapeTM.indicator
        split_ifs with hm <;> cases hb : (u n).getD h false <;> simp_all
      have hbd : ∀ j ≤ t, Bd B (CounterProg.run P (u n) (CounterProg.init l₀) j) := by
        intro j hj
        have hjN : j ≤ N := hj.trans ht
        have hNB : N * (N + 1) ≤ B := by simp only [hB]; nlinarith
        have hNN : N ≤ N * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
        refine ⟨fun r => ?_, ?_, ?_⟩
        · have := CounterProg.run_regs_le P (u n) (CounterProg.init l₀) r j
          have h0 : (CounterProg.init l₀ : CounterProg.St R Λ).regs r = 0 := rfl
          omega
        · have := CounterProg.run_pos_le P (u n) (CounterProg.init l₀) j
          have h0 : (CounterProg.init l₀ : CounterProg.St R Λ).pos = 0 := rfl
          omega
        · have := CounterProg.run_init_out_le P (u n) l₀ j
          have : j * (j + 1) ≤ N * (N + 1) := Nat.mul_le_mul hjN (by omega)
          omega
      have hrunA := sim_run (P := P) (l₀ := l₀) (lm := lm) (B := B) (n := n) (p := p)
        (o := fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) ho0 ho1 t
        (CounterProg.init l₀) 0 l₀ rfl (by simp [CounterProg.init]) (Nat.zero_le _) hhalt hbd
      rw [hout] at hrunA
      have hans : ans lm (g n) p = MultiTapeTM.indicator
          ((if lm then uLen g else uBit g : Language Bool) : Set (List Bool))
          (pairEncode (List.replicate n true) (Nat.bits p)) := by
        cases lm
        · show (g n).getD p false = MultiTapeTM.indicator (uBit g : Set (List Bool)) _
          have := mem_uBit g n p
          unfold MultiTapeTM.indicator
          split_ifs with hm <;> cases hb : (g n).getD p false <;> simp_all
        · show decide (p < (g n).length) = MultiTapeTM.indicator (uLen g : Set (List Bool)) _
          have := mem_uLen g n p
          unfold MultiTapeTM.indicator
          split_ifs with hm <;> simp_all
      rw [← hans]
      have hval : ValidPlain (pairEncode (List.replicate n true) (Nat.bits p)) :=
        ⟨n, _, rfl, canon_bits p⟩
      have hev : (fun _ => 0 : Fin (R + 3) → ℕ) =
          ev (CounterProg.init l₀ : CounterProg.St R Λ).regs (CounterProg.init l₀ :
            CounterProg.St R Λ).pos (CounterProg.init l₀ : CounterProg.St R Λ).out.length 0 := by
        funext i; simp only [ev, CounterProg.init]; split_ifs <;> rfl
      refine AHalt.step ⟨preS_A P l₀ lm hval _, fun r => by simp⟩ ?_
      have : astep (A P l₀ lm) (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V)
          (pairEncode (List.replicate n true) (Nat.bits p)) (some .start, fun _ => 0, none) =
          cf (.sim l₀) (ev (CounterProg.init l₀ : CounterProg.St R Λ).regs
            (CounterProg.init l₀ : CounterProg.St R Λ).pos
            (CounterProg.init l₀ : CounterProg.St R Λ).out.length 0) := by
        rw [← hev]; simp [astep, A, hval]
      rw [this]
      refine hrunA.mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => (h2 r).trans ?_⟩
      have hn : n + 1 ≤ (pairEncode (List.replicate n true) (Nat.bits p)).length + 1 := by
        simp [pairEncode_eq_dbl, dbl_replicate]; omega
      have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
      calc B = (C * (n + 1) ^ c + 1) ^ 2 := rfl
        _ ≤ ((C + 1) * (n + 1) ^ c) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
        _ = (C + 1) ^ 2 * (n + 1) ^ (2 * c) := by ring
        _ ≤ (C + 1) ^ 2 * ((pairEncode (List.replicate n true) (Nat.bits p)).length + 1) ^
            (2 * c) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
    · have hn : MultiTapeTM.indicator ((if lm then uLen g else uBit g : Language Bool) :
          Set (List Bool)) y = false := by
        rw [indicator_eq_decide]
        simp only [decide_eq_false_iff_not]
        intro h
        cases lm
        · exact hv (validPlain_of_mem_unaryIdx (p := fun n i => (g n).getD i false = true) h)
        · exact hv (validPlain_of_mem_unaryIdx (p := fun n i => i < (g n).length) h)
      rw [hn]
      refine ⟨1, ?_, ?_, fun t ht => ?_⟩
      · simp [arun, astep, A, hv]
      · simp [arun, astep, A, hv]
      · obtain rfl : t = 0 := by omega
        exact ⟨by simp [arun, PreS, A], fun r => by simp [arun]⟩
  exact ⟨by simpa using key false, by simpa using key true⟩

end Complexity
