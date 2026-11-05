/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.SpaceClasses

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines with wide registers

`Complexity.LogProg.arm_decides` turns a correct abstract register machine whose registers
hold `O(log |x|)` binary digits, calling logspace deciders, into a logspace decider. The run
and space theorem behind it (`Complexity.LogProg.arm_space`) allows any register width `W`;
only the wrapper fixes `W = O(log n)`. This file gives the wrappers for wider registers: a
general one (`Complexity.LogProg.arm_decides_space`, into `SPACE S`), and the polynomial-width
and `S`-width forms consumed by polynomial-space and Savitch-type arguments.

This is infrastructure — the register-machine description of space-bounded algorithms of
[AB09, §4.1] extended to `S(n) ≥ log n` registers — not itself a result of the book.

## Main definitions

* none (wrapper theorems for `Complexity.LogProg.ARM`, and the inclusions `L ⊆ PSPACE` and
  `SPACE ((n + 1)^k) ⊆ PSPACE`).

## Main results

* `Complexity.LogProg.arm_decides_space` — the general wrapper: registers of `W(|x|)` binary
  digits, deciders using space `s_j`, both `O(S(|x|))` on the relevant lengths, give `SPACE S`.
* `Complexity.LogProg.arm_decides_SPACE` — registers of `O(S(|x|))` binary digits with
  logspace deciders, for `S ≥ logSpace`, give `SPACE S`.
* `Complexity.LogProg.arm_decides_pspace` — registers of polynomially many binary digits with
  `PSPACE` deciders give `PSPACE`; `Complexity.LogProg.arm_decides_pspace_of_logspace` and
  `Complexity.LogProg.arm_decides_pspace_val` are its logspace-decider and value-bound forms.
* `Complexity.LOGSPACE_subset_PSPACE` — `L ⊆ PSPACE`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5.)
-/

namespace Complexity

/-- The logarithmic bound is at most linear: `logSpace n ≤ n + 1`. -/
lemma logSpace_le_succ (n : ℕ) : logSpace n ≤ n + 1 := by
  have := Nat.log_le_self 2 n
  simp only [logSpace]; omega

/-- **`L ⊆ PSPACE`** [AB09, §4.1.2, the chain `L ⊆ … ⊆ PSPACE` of p. 92 (its first and
last members)]: a logspace decider uses at most `c · (n + 1)` cells.

**Proof sketch.** `logSpace n ≤ n + 1 = n ^ 1 + 1`, so `SPACE (logSpace) ⊆ SPACE (n ^ 1 + 1)`
(`Complexity.SPACE.mono`), which lies in `PSPACE` at degree one. -/
theorem LOGSPACE_subset_PSPACE : LOGSPACE ⊆ PSPACE :=
  (SPACE.mono fun n => by simpa using logSpace_le_succ n).trans (space_poly_subset_PSPACE 1)

/-- `SPACE ((n + 1)^k) ⊆ PSPACE`: the shifted polynomial bound gives polynomial space.

**Proof sketch.** `(n + 1)^k ≤ 2^k (n^k + 1)` (`Complexity.succ_pow_le`), so
`Complexity.SPACE.mono_const` and `Complexity.space_poly_subset_PSPACE` at degree `k`. -/
theorem SPACE_succ_pow_subset_PSPACE (k : ℕ) : SPACE (fun n => (n + 1) ^ k) ⊆ PSPACE :=
  (SPACE.mono_const (a := 2 ^ k) fun n => succ_pow_le n k).trans
    (space_poly_subset_PSPACE k)

/-- A number at most `A · 2^s` (with `s ≥ 1`) has `logSpace` at most `(A + 1) s`. -/
lemma logSpace_le_of_le_mul_two_pow {v A s : ℕ} (h : v ≤ A * 2 ^ s) (hs : 1 ≤ s) :
    logSpace v ≤ (A + 1) * s := by
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hlt : v < 2 ^ (A + s) := by
    rw [pow_add]
    exact lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos s))
  have hle : A + s ≤ (A + 1) * s := by
    have := Nat.le_mul_of_pos_right A (show 0 < s by omega)
    rw [Nat.add_mul, Nat.one_mul]; omega
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp only [logSpace, Nat.log_zero_right]; omega
  · have := Nat.log_lt_of_lt_pow (by omega) hlt
    simp only [logSpace]; omega

end Complexity

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type}

/-- **Abstract register machines with registers of `W(|x|)` binary digits decide languages in
`SPACE S`** (general width): if, on every input `x`, the abstract machine `A`, calling
deciders for the languages `As j` that run in space `s j`, answers `x ∈ L` through
configurations meeting the syntactic preconditions with every register value of at most
`W |x|` binary digits (counting one increment), and both the register width and the
deciders' space on every virtual input a call can form (of length at most
`2|x| + 2 + m (2 W |x| + 2)`, `Complexity.LogProg.length_callSegs_le`) are at most
`C · S |x|`, with `S ≥ 1`, then `L ∈ SPACE S`. Infrastructure for [AB09, §4.1]; at
`S = W = O(logSpace)` it is `Complexity.LogProg.arm_decides`.

**Proof sketch.** As for `Complexity.LogProg.arm_decides`: collect the deciders in a clean
bank (`Complexity.LogProg.bank_cleanRun`); the virtual inputs are short
(`Complexity.LogProg.length_callSegs_le`), so the deciders' head ranges are at most
`B = C · S |x| + 1`; `Complexity.LogProg.arm_space` then gives a machine answering `x ∈ L`
within `m (W + 2) + k_D (2B + 1) ≤ (m C + 2m + k_D (2C + 3)) · S |x|` cells. -/
theorem arm_decides_space {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (s : Fin d → ℕ → ℕ)
    (hAs : ∀ j, ∃ M : FinTM Bool, M.DecidesInSpace (As j) (s j))
    (S W : ℕ → ℕ) (C : ℕ) (hS : ∀ n, 1 ≤ S n) (hW : ∀ n, W n ≤ C * S n)
    (hs : ∀ j n v, v ≤ 2 * n + 2 + m * (2 * W n + 2) → s j v ≤ C * S n)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ W x.length)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ SPACE S := by
  classical
  let Ms : Fin d → FinTM Bool := fun j => Classical.choose (hAs j)
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) (s j) := fun j => Classical.choose_spec (hAs j)
  set kD := bankK Ms + bankK Ms with hkD
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  refine ⟨m * C + 2 * m + kD * (2 * C + 3),
    compileFinTM (armProg A l₀) (l₀, .start) (bankTM Ms) (bankStart Ms), fun x => ?_⟩
  set n := x.length with hn
  have hS1 := hS n
  set B := C * S n + 1 with hB
  obtain ⟨N, h1, h2, hm⟩ := hcorr x
  -- the preconditions of `arm_space`: syntactic ones, clean decider runs within `B`
  have hpre : ∀ t < N, Pre A oracle (bankTM Ms) (bankStart Ms) B x
      (arun A oracle x (some l₀, fun _ => 0, none) t) ∧
      ∀ r, ((Nat.bits ((arun A oracle x (some l₀, fun _ => 0, none) t).2.1 r + 1)).length : ℤ)
        ≤ ((W n : ℕ) : ℤ) := by
    intro t ht
    obtain ⟨hps, hbd⟩ := hm t ht
    refine ⟨?_, fun r => by exact_mod_cast hbd r⟩
    generalize hat : arun A oracle x (some l₀, fun _ => 0, none) t = a at hps hbd
    rcases a with ⟨_ | l, v, res⟩
    · trivial
    · simp only [Pre]
      cases hA : A l with
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
      refine cleanRun_mono (bank_cleanRun Ms As s hMs j _) ?_
      have hVl := length_callSegs_le (x := x) ⟨j, md, args, l₁, l₀'⟩ (W n)
        (fun r => Nat.bits (v r))
        (fun r => by
          show (Nat.bits (v r)).length ≤ W n
          have h0 : (Nat.bits (v r + 1)).length ≤ W n := hbd r
          have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length :=
            length_bits_mono (by omega)
          omega) hps
      have := hs j n _ hVl
      simp only [hB]
      exact max_le (by omega) (by omega)
  obtain ⟨T, hT, hsp⟩ := arm_space A l₀ oracle (bankTM Ms) (bankStart Ms) B (W n) N
    (MultiTapeTM.indicator (L : Set (List Bool)) x) h1 h2 hpre
  refine ⟨T, hT, hsp.trans ?_⟩
  -- the arithmetic: `m (W + 2) + k_D (2B + 1) ≤ (m C + 2m + k_D (2C + 3)) S`
  show _ ≤ (m * C + 2 * m + kD * (2 * C + 3)) * S n
  have f0 : m * W n ≤ m * (C * S n) := Nat.mul_le_mul_left m (hW n)
  have e1 : m * (W n + 2) = m * W n + 2 * m := by ring
  have e2 : kD * (2 * B + 1) = 2 * kD * C * S n + 3 * kD := by simp only [hB]; ring
  have e3 : (m * C + 2 * m + kD * (2 * C + 3)) * S n =
      m * (C * S n) + 2 * m * S n + 2 * kD * C * S n + 3 * kD * S n := by ring
  rw [e1, e2, e3]
  have f1 : 2 * m ≤ 2 * m * S n := Nat.le_mul_of_pos_right _ (by omega)
  have f2 : 3 * kD ≤ 3 * kD * S n := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **Abstract register machines with `O(S)`-digit registers and logspace subroutines decide
languages in `SPACE S`**: for `S ≥ logSpace`, if on every input `x` the abstract machine `A`,
calling deciders for languages in `L`, answers `x ∈ L` through configurations meeting the
syntactic preconditions with every register value of at most `K · S |x|` binary digits
(counting one increment), then `L ∈ SPACE S`. Infrastructure for [AB09, §4.1]
(`S(n) ≥ log n`, the book's standing convention, p. 79); no monotonicity or constructibility
of `S` is needed.

**Proof sketch.** `Complexity.LogProg.arm_decides_space` with `W = K · S`. A virtual input
has length `v ≤ 2|x| + 2 + m (2 K S + 2) ≤ A · 2^S` (as `|x| < 2^{logSpace |x|} ≤ 2^S` and
`S < 2^S`), so a logspace decider uses `c · logSpace v ≤ c (A + 1) · S` cells
(`Complexity.logSpace_le_of_le_mul_two_pow`). -/
theorem arm_decides_SPACE {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (S : ℕ → ℕ)
    (hS : ∀ n, logSpace n ≤ S n) (K : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ K * S x.length)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ SPACE S := by
  classical
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  let c : Fin d → ℕ := fun j => Classical.choose (hc j)
  have hc' : ∀ j, ∃ M : FinTM Bool, M.DecidesInSpace (As j) fun n => c j * logSpace n :=
    fun j => Classical.choose_spec (hc j)
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set A₀ := 2 + 2 * m + 2 * m * K with hA₀
  have hS1 : ∀ n, 1 ≤ S n := fun n => le_trans (by simp [logSpace]) (hS n)
  refine arm_decides_space A l₀ As (fun j n => c j * logSpace n) hc' S (fun n => K * S n)
    (K + cs * (A₀ + 1)) hS1 (fun n => Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    (fun j n v hv => ?_) hcorr
  -- a virtual input has length at most `A₀ · 2^S`
  set P := 2 ^ S n with hP
  have hnP : n + 1 ≤ P :=
    (succ_le_two_pow_log n).trans (Nat.pow_le_pow_right (by norm_num) (hS n))
  have hSP : S n ≤ P := (Nat.lt_two_pow_self).le
  have hvP : v ≤ A₀ * P := by
    have g1 : m * K * S n ≤ m * K * P := Nat.mul_le_mul_left _ hSP
    have g2 : m ≤ m * P := Nat.le_mul_of_pos_right _ (by omega)
    have e1 : m * (2 * (K * S n) + 2) = 2 * (m * K * S n) + 2 * m := by ring
    have e2 : A₀ * P = 2 * P + 2 * (m * P) + 2 * (m * K * P) := by simp only [hA₀]; ring
    rw [e1] at hv; rw [e2]; omega
  have hlog := logSpace_le_of_le_mul_two_pow hvP (hS1 n)
  calc c j * logSpace v ≤ cs * ((A₀ + 1) * S n) := Nat.mul_le_mul (hcj j) hlog
    _ = cs * (A₀ + 1) * S n := by ring
    _ ≤ (K + cs * (A₀ + 1)) * S n := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- **Abstract register machines with polynomially wide registers decide languages in
`PSPACE`**: if, on every input `x`, the abstract machine `A`, calling deciders for languages
in `PSPACE`, answers `x ∈ L` through configurations meeting the syntactic preconditions with
every register value of at most `C₀ (|x| + 1)^{c₀}` binary digits (counting one increment),
then `L ∈ PSPACE`. Infrastructure for [AB09, §4.1, Definition 4.5].

**Proof sketch.** Each decider `j` runs in space `c_j (n^{e_j} + 1)`. A virtual input has
length `v ≤ A (|x| + 1)^{c₀ + 1}`, so decider `j` uses at most
`c_j (A^{e_j} + 1) (|x| + 1)^{(c₀ + 1) e_j}` cells. With `E = (c₀ + 1)(Σ e_j + 1)`,
`Complexity.LogProg.arm_decides_space` at `S = (n + 1)^E` gives `L ∈ SPACE ((n + 1)^E)`,
inside `PSPACE` (`Complexity.SPACE_succ_pow_subset_PSPACE`). -/
theorem arm_decides_pspace {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ PSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧
        ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ PSPACE := by
  classical
  have hc : ∀ j, ∃ (e c : ℕ) (M : FinTM Bool),
      M.DecidesInSpace (As j) fun n => c * (n ^ e + 1) := fun j => by
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp (hAs j)
    exact ⟨e, he⟩
  let e : Fin d → ℕ := fun j => Classical.choose (hc j)
  let c : Fin d → ℕ := fun j => Classical.choose (Classical.choose_spec (hc j))
  have hc' : ∀ j, ∃ M : FinTM Bool, M.DecidesInSpace (As j) fun n => c j * (n ^ e j + 1) :=
    fun j => Classical.choose_spec (Classical.choose_spec (hc j))
  set A₀ := 2 + 2 * m + 2 * m * C₀ with hA₀
  set es := ∑ j, e j with hes
  set E := (c₀ + 1) * (es + 1) with hE
  set C := C₀ + ∑ j, c j * (A₀ ^ e j + 1) with hC
  have hej : ∀ j, e j ≤ es := fun j =>
    Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hcj : ∀ j, c j * (A₀ ^ e j + 1) ≤ C := fun j =>
    (Finset.single_le_sum (f := fun j => c j * (A₀ ^ e j + 1)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans (Nat.le_add_left _ _)
  have hc₀E : c₀ + 1 ≤ E := Nat.le_mul_of_pos_right _ (by omega)
  have hpowE : ∀ n k, k ≤ E → (n + 1) ^ k ≤ (n + 1) ^ E := fun n k hk =>
    Nat.pow_le_pow_right (by omega) hk
  refine SPACE_succ_pow_subset_PSPACE E (arm_decides_space A l₀ As
    (fun j n => c j * (n ^ e j + 1)) hc' (fun n => (n + 1) ^ E) (fun n => C₀ * (n + 1) ^ c₀) C
    (fun n => Nat.one_le_pow _ _ (by omega))
    (fun n => Nat.mul_le_mul (Nat.le_add_right _ _) (hpowE n c₀ (by omega)))
    (fun j n v hv => ?_) hcorr)
  -- a virtual input has length at most `A₀ (n + 1)^{c₀ + 1}`
  set P := (n + 1) ^ (c₀ + 1) with hP
  have hP1 : n + 1 ≤ P := by
    simpa using Nat.pow_le_pow_right (show 0 < n + 1 by omega) (show 1 ≤ c₀ + 1 by omega)
  have hPc : (n + 1) ^ c₀ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hvP : v ≤ A₀ * P := by
    have g1 : m * C₀ * (n + 1) ^ c₀ ≤ m * C₀ * P := Nat.mul_le_mul_left _ hPc
    have g2 : m ≤ m * P := Nat.le_mul_of_pos_right _ (by omega)
    have e1 : m * (2 * (C₀ * (n + 1) ^ c₀) + 2) = 2 * (m * C₀ * (n + 1) ^ c₀) + 2 * m := by
      ring
    have e2 : A₀ * P = 2 * P + 2 * (m * P) + 2 * (m * C₀ * P) := by simp only [hA₀]; ring
    rw [e1] at hv; rw [e2]; omega
  -- decider `j` uses at most `c_j (A₀^{e_j} + 1) (n + 1)^E` cells
  have hpow : v ^ e j + 1 ≤ (A₀ ^ e j + 1) * (n + 1) ^ E := by
    have h1 : v ^ e j ≤ A₀ ^ e j * (n + 1) ^ E := by
      calc v ^ e j ≤ (A₀ * P) ^ e j := Nat.pow_le_pow_left hvP _
        _ = A₀ ^ e j * (n + 1) ^ ((c₀ + 1) * e j) := by rw [mul_pow, hP, ← pow_mul]
        _ ≤ A₀ ^ e j * (n + 1) ^ E := Nat.mul_le_mul_left _ (hpowE n _
          (Nat.mul_le_mul_left _ ((hej j).trans (Nat.le_succ _))))
    have h2 : 1 ≤ (n + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    rw [Nat.add_mul, Nat.one_mul]; omega
  calc c j * (v ^ e j + 1) ≤ c j * ((A₀ ^ e j + 1) * (n + 1) ^ E) := Nat.mul_le_mul_left _ hpow
    _ = c j * (A₀ ^ e j + 1) * (n + 1) ^ E := by ring
    _ ≤ C * (n + 1) ^ E := Nat.mul_le_mul_right _ (hcj j)

/-- **Polynomially wide registers with logspace subroutines give `PSPACE`**: the form of
`Complexity.LogProg.arm_decides_pspace` with deciders in `L`. Infrastructure for [AB09, §4.1].

**Proof sketch.** `L ⊆ PSPACE` (`Complexity.LOGSPACE_subset_PSPACE`). -/
theorem arm_decides_pspace_of_logspace {L : Language Bool} [Fintype Λ] [DecidableEq Λ]
    (A : ARM m d Λ) (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE)
    (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧
        ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ PSPACE :=
  arm_decides_pspace A l₀ As (fun j => LOGSPACE_subset_PSPACE (hAs j)) C₀ c₀ hcorr

/-- **Exponentially large register values give `PSPACE`**: the form of
`Complexity.LogProg.arm_decides_pspace` with register values at most
`2^{C₀ (|x| + 1)^{c₀}}`. Infrastructure for [AB09, §4.1].

**Proof sketch.** A value `v ≤ 2^N` has `v + 1 < 2^{N + 2}`, so `|bits (v + 1)| ≤ N + 2
≤ (C₀ + 2)(|x| + 1)^{c₀}` (`Complexity.LogProg.length_bits_le`). -/
theorem arm_decides_pspace_val {L : Language Bool} [Fintype Λ] [DecidableEq Λ]
    (A : ARM m d Λ) (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ PSPACE)
    (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ 2 ^ (C₀ * (x.length + 1) ^ c₀))
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ PSPACE := by
  refine arm_decides_pspace A l₀ As hAs (C₀ + 2) c₀ fun x =>
    (hcorr x).mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => ?_⟩
  set N := C₀ * (x.length + 1) ^ c₀ with hN
  have hlt : a.2.1 r + 1 < 2 ^ (N + 2) := by
    have := h2 r
    have e : 2 ^ (N + 2) = 4 * 2 ^ N := by rw [pow_add]; ring
    have := Nat.two_pow_pos N
    omega
  have h3 := length_bits_le hlt
  have h4 : 2 ≤ 2 * (x.length + 1) ^ c₀ :=
    Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
  have e : (C₀ + 2) * (x.length + 1) ^ c₀ = N + 2 * (x.length + 1) ^ c₀ := by
    simp only [hN]; ring
  omega

end Complexity.LogProg
