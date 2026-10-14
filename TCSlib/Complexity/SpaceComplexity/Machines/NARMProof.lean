/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.SpaceClasses

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic abstract register machines decide languages in `NL` and `NPSPACE`

The bridges from correct nondeterministic abstract register machines
(`Complexity.LogProg.NARM`) to the nondeterministic space classes: a machine that, on every
input `x`, halts on every branch of some length `N` through configurations meeting the
syntactic preconditions with registers of bounded width, and has a branch answering `true`
exactly when `x ∈ L`, places `L` in

* `NSPACE S`, for registers of `O(S)` digits and deciders whose space on the possible virtual
  inputs is `O(S)` (`Complexity.LogProg.narm_decides_space`);
* `NL`, for registers of `O(log n)` digits (or values polynomial in `n`) and logspace deciders
  (`Complexity.LogProg.narm_decides`, `Complexity.LogProg.narm_decides_poly`) — the
  nondeterministic form of `Complexity.LogProg.arm_decides`;
* `NPSPACE`, for registers of polynomially many digits and `PSPACE` (or logspace) deciders
  (`Complexity.LogProg.narm_decides_npspace`,
  `Complexity.LogProg.narm_decides_npspace_of_logspace`).

This is infrastructure for [AB09, §4.1–4.3] (the register-machine descriptions of
nondeterministic space-bounded algorithms), not itself a result of the book.

## Main definitions

* none (bridges only; the machine model is in
  `TCSlib.Complexity.SpaceComplexity.Machines.NARM`).

## Main results

* `Complexity.LogProg.narm_decides_space`, `Complexity.LogProg.narm_decides`,
  `Complexity.LogProg.narm_decides_poly`, `Complexity.LogProg.narm_decides_npspace`,
  `Complexity.LogProg.narm_decides_npspace_of_logspace`.
* `Complexity.NSPACE.mono_const` — `NSPACE` absorbs constant factors.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5.)
-/

namespace Complexity

/-- `NSPACE` absorbs constant factors: if `s₁ ≤ a · s₂` pointwise, then
`NSPACE s₁ ⊆ NSPACE s₂`. [AB09, Definition 4.1: the constant `c` absorbs `a`]

**Proof sketch.** A witness at constant `c` for `s₁` is a witness at constant `c · a` for
`s₂`, with the same budgets, since `c · s₁ n ≤ (c · a) · s₂ n`. -/
theorem NSPACE.mono_const {s₁ s₂ : ℕ → ℕ} {a : ℕ} (h : ∀ n, s₁ n ≤ a * s₂ n) :
    NSPACE s₁ ⊆ NSPACE s₂ := by
  rintro L ⟨c, N, hN⟩
  refine ⟨c * a, N, fun x => ?_⟩
  obtain ⟨T, h1, h2, h3⟩ := hN x
  refine ⟨T, h1, fun w hw => (h2 w hw).trans ?_, h3⟩
  calc c * s₁ x.length ≤ c * (a * s₂ x.length) := Nat.mul_le_mul_left c (h _)
    _ = c * a * s₂ x.length := (Nat.mul_assoc c a _).symm

end Complexity

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- **The preconditions from the syntactic ones**: with the deciders collected in a clean bank,
a configuration meeting the syntactic preconditions, with register values of at most `Wd`
binary digits (counting one increment), meets the preconditions `NPre` at decider head range
`B`, provided every decider's space on the virtual inputs a call can form (of length at most
`2|x| + 2 + m (2 Wd + 2)`, `length_callSegs_le`) is at most `B`, and `B ≥ 1`.

**Proof sketch.** Case analysis on the instruction; at a call the bank answers cleanly within
`max (s j |V|) 1` (`bank_cleanRun`), and the virtual input `V` is short. -/
lemma npre_of_npreS (A : NARM m d Λ) (Ms : Fin d → FinTM Bool) (As : Fin d → Language Bool)
    (s : Fin d → ℕ → ℕ) (hMs : ∀ j, (Ms j).DecidesInSpace (As j) (s j)) (B Wd : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ j n, n ≤ 2 * x.length + 2 + m * (2 * Wd + 2) → s j n ≤ B)
    (a : AConf m Λ) (hps : NPreS A x a) (hbd : ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ Wd) :
    NPre A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) (bankTM Ms)
      (bankStart Ms) B x a := by
  unfold NPre
  unfold NPreS at hps
  generalize A.detPart false = A' at hps ⊢
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · simp only [Pre]
    cases hA : A' l with
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
      refine ⟨hps, cleanRun_mono (bank_cleanRun Ms As s hMs j _) ?_⟩
      have hVl := length_callSegs_le (x := x) ⟨j, md, args, l₁, l₀'⟩ Wd
        (fun r => Nat.bits (v r))
        (fun r => by
          show (Nat.bits (v r)).length ≤ Wd
          have h0 : (Nat.bits (v r + 1)).length ≤ Wd := hbd r
          have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length :=
            length_bits_mono (by omega)
          omega) hps
      exact max_le (hB j _ hVl) hB1

/-- **Nondeterministic abstract register machines with registers of `W(|x|)` binary digits
decide languages in `NSPACE S`** (general width): if, on every input `x`, for some `N` every
choice word of length `N` halts the machine `A` (calling deciders for the languages `As j`
that run in space `s j`) through configurations meeting the syntactic preconditions with every
register value of at most `W |x|` binary digits (counting one increment), and `x ∈ L` iff
some choice word of length `N` answers `true`, and both the register width and the deciders'
space on every virtual input a call can form are at most `C · S |x|`, with `S ≥ 1`, then
`L ∈ NSPACE S`. Infrastructure for [AB09, §4.1]; the nondeterministic form of
`Complexity.LogProg.arm_decides_space`.

**Proof sketch.** Collect the deciders in a clean bank (`bank_cleanRun`); the preconditions
hold with decider head range `B = C · S |x| + 1` (`npre_of_npreS`); `narm_space` gives a
nondeterministic machine all of whose branches halt within
`m (W + 2) + kD (2B + 1) ≤ (m C + 2m + kD (2C + 3)) · S |x|` cells, some branch accepting iff
`x ∈ L`. -/
theorem narm_decides_space {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : NARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (s : Fin d → ℕ → ℕ)
    (hAs : ∀ j, ∃ M : FinTM Bool, M.DecidesInSpace (As j) (s j))
    (S W : ℕ → ℕ) (C : ℕ) (hS : ∀ n, 1 ≤ S n) (hW : ∀ n, W n ≤ C * S n)
    (hs : ∀ j n v, v ≤ 2 * n + 2 + m * (2 * W n + 2) → s j v ≤ C * S n)
    (hcorr : ∀ x, ∃ N,
      NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ W x.length)
        (some l₀, fun _ => 0, none) N ∧
      (x ∈ L ↔ NAns A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N true)) :
    L ∈ NSPACE S := by
  classical
  let Ms : Fin d → FinTM Bool := fun j => Classical.choose (hAs j)
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) (s j) := fun j => Classical.choose_spec (hAs j)
  set kD := bankK Ms + bankK Ms with hkD
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  refine ⟨m * C + 2 * m + kD * (2 * C + 3),
    ncompileFinNDTM A l₀ (bankTM Ms) (bankStart Ms), fun x => ?_⟩
  set n := x.length with hn
  have hS1 := hS n
  set B := C * S n + 1 with hB
  obtain ⟨N, hN, hL⟩ := hcorr x
  have hG : NHalts A oracle x (NGuard A oracle (bankTM Ms) (bankStart Ms) B (W n) x)
      (some l₀, fun _ => 0, none) N :=
    hN.mono fun a ⟨hps, hbd⟩ =>
      ⟨npre_of_npreS A Ms As s hMs B (W n) (by omega)
        (fun j v hv => by have := hs j n v hv; omega) a hps hbd,
       fun r => by exact_mod_cast hbd r⟩
  obtain ⟨T, hhalt, hsp, hacc⟩ :=
    narm_space A l₀ oracle (bankTM Ms) (bankStart Ms) B (W n) N hG
  refine ⟨T, hhalt, fun w hw => (hsp w hw).trans ?_, hL.trans hacc⟩
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

/-- **Nondeterministic abstract register machines with logarithmic registers decide languages
in `NL`**: if, on every input `x`, for some `N` every choice word of length `N` halts the
machine `A` (calling deciders for languages in `L`) through configurations meeting the
syntactic preconditions with every register value of at most `K · logSpace |x|` binary digits
(counting one increment), and `x ∈ L` iff some choice word of length `N` answers `true`, then
`L ∈ NL`. Infrastructure for [AB09, §4.3] (nondeterministic logspace algorithms that guess);
the nondeterministic form of `Complexity.LogProg.arm_decides`.

**Proof sketch.** `narm_decides_space` at `S = logSpace`. A virtual input has length at most
`2|x| + 2 + m (2 K logSpace |x| + 2) ≤ Q (|x| + 1)`, so a decider in space
`c_j · logSpace` uses at most `c_j K₂ logSpace |x|` cells (`log_poly_bound`). -/
theorem narm_decides {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : NARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (K : ℕ)
    (hcorr : ∀ x, ∃ N,
      NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ K * logSpace x.length)
        (some l₀, fun _ => 0, none) N ∧
      (x ∈ L ↔ NAns A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N true)) :
    L ∈ NL := by
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  choose c Ms hMs using hc
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Q := 4 + 2 * m + 2 * m * K with hQ
  obtain ⟨K2, hK2⟩ := log_poly_bound Q 1 0
  refine narm_decides_space A l₀ As (fun j n => c j * logSpace n) (fun j => ⟨Ms j, hMs j⟩)
    logSpace (fun n => K * logSpace n) (K + cs * K2) (fun n => by simp [logSpace])
    (fun n => Nat.mul_le_mul_right _ (by omega)) (fun j n v hv => ?_) hcorr
  beta_reduce at hv ⊢
  have hLn : logSpace n ≤ n + 1 := by
    have := Nat.log_le_self 2 n
    simp only [logSpace]; omega
  have hVQ : v ≤ Q * (n + 1) ^ 1 + 0 := by
    have hW : K * logSpace n ≤ K * (n + 1) := Nat.mul_le_mul_left K hLn
    have e : Q * (n + 1) ^ 1 + 0 = (4 + 2 * m) * (n + 1) + 2 * m * (K * (n + 1)) := by
      simp only [hQ]; ring
    rw [e]
    have h5 : m * (2 * (K * logSpace n) + 2) ≤ 2 * m * (K * (n + 1)) + 2 * m := by
      have := Nat.mul_le_mul_left (2 * m) hW
      calc m * (2 * (K * logSpace n) + 2) = 2 * m * (K * logSpace n) + 2 * m := by ring
        _ ≤ 2 * m * (K * (n + 1)) + 2 * m := by omega
    have h6 : 2 * m ≤ 2 * m * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h7 : (4 + 2 * m) * (n + 1) = 4 * (n + 1) + 2 * m * (n + 1) := by ring
    omega
  have hlog : logSpace v ≤ K2 * logSpace n := by
    have h := hK2 n
    have hm' := Nat.log_mono_right (b := 2) hVQ
    simp only [logSpace] at h hm' ⊢
    omega
  calc c j * logSpace v ≤ cs * (K2 * logSpace n) :=
        Nat.mul_le_mul (hcj j) hlog
    _ ≤ (K + cs * K2) * logSpace n := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)

/-- **Nondeterministic abstract register machines with polynomially bounded registers decide
languages in `NL`**: the form of `narm_decides` with register values at most
`C₀ (|x| + 1)^{c₀}`. Infrastructure for [AB09, §4.3].

**Proof sketch.** A value `v ≤ C₀ (|x|+1)^{c₀}` has `|bits (v + 1)| ≤ ⌊log₂ (v + 1)⌋ + 1`,
which `log_poly_bound` bounds by `K · logSpace |x|`. -/
theorem narm_decides_poly {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : NARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, ∃ N,
      NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
        (some l₀, fun _ => 0, none) N ∧
      (x ∈ L ↔ NAns A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N true)) :
    L ∈ NL := by
  obtain ⟨K, hK⟩ := log_poly_bound C₀ c₀ 1
  refine narm_decides A l₀ As hAs K fun x => ?_
  obtain ⟨N, hN, hL⟩ := hcorr x
  refine ⟨N, hN.mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => ?_⟩, hL⟩
  have e1 := length_bits_le_log (a.2.1 r + 1)
  have e2 : Nat.log 2 (a.2.1 r + 1) ≤ Nat.log 2 (C₀ * (x.length + 1) ^ c₀ + 1) :=
    Nat.log_mono_right (by have := h2 r; omega)
  have e3 := hK x.length
  simp only [logSpace]
  omega

/-- **Nondeterministic abstract register machines with polynomially wide registers decide
languages in `NPSPACE`**: if, on every input `x`, for some `N` every choice word of length `N`
halts the machine `A` (calling deciders for languages in `PSPACE`) through configurations
meeting the syntactic preconditions with every register value of at most
`C₀ (|x| + 1)^{c₀}` binary digits (counting one increment), and `x ∈ L` iff some choice word
of length `N` answers `true`, then `L ∈ NPSPACE`. Infrastructure for [AB09, §4.1,
Definition 4.5]; the nondeterministic form of `Complexity.LogProg.arm_decides_pspace`.

**Proof sketch.** Decider `j` runs in space `c_j (n^{e_j} + 1)`. A virtual input has length
`v ≤ A₀ (|x| + 1)^{c₀ + 1}`, so decider `j` uses at most `c_j (A₀^{e_j} + 1) (|x| + 1)^E`
cells, `E = (c₀ + 1)(Σ e_j + 1)`. `narm_decides_space` at `S = (n + 1)^E` gives
`L ∈ NSPACE ((n + 1)^E)`, inside `NSPACE (n^E + 1)` up to the factor `2^E`
(`NSPACE.mono_const`). -/
theorem narm_decides_npspace {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : NARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ PSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, ∃ N,
      NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧
          ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ C₀ * (x.length + 1) ^ c₀)
        (some l₀, fun _ => 0, none) N ∧
      (x ∈ L ↔ NAns A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N true)) :
    L ∈ NPSPACE := by
  have hc : ∀ j, ∃ (e c : ℕ) (M : FinTM Bool),
      M.DecidesInSpace (As j) fun n => c * (n ^ e + 1) := by
    intro j
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp (hAs j)
    obtain ⟨c, M, hM⟩ := he
    exact ⟨e, c, M, hM⟩
  choose e c Ms hMs using hc
  set A₀ := 2 + 2 * m * C₀ + 2 * m with hA₀
  set E := (c₀ + 1) * (∑ j, e j + 1) with hE
  set Cc := C₀ + ∑ j, c j * (A₀ ^ e j + 1) with hCc
  have hc₀E : c₀ ≤ E := by
    have : c₀ + 1 ≤ E := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hejE : ∀ j, (c₀ + 1) * e j ≤ E := fun j => by
    refine Nat.mul_le_mul_left _ ?_
    have := Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hsub : L ∈ NSPACE fun n => (n + 1) ^ E := by
    refine narm_decides_space A l₀ As (fun j v => c j * (v ^ e j + 1))
      (fun j => ⟨Ms j, hMs j⟩) (fun n => (n + 1) ^ E) (fun n => C₀ * (n + 1) ^ c₀) Cc
      (fun n => Nat.one_le_pow _ _ (Nat.succ_pos n)) (fun n => ?_) (fun j n v hv => ?_) hcorr
    · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (Nat.succ_pos n) hc₀E)
    · -- the virtual inputs are polynomially long
      beta_reduce at hv ⊢
      set P := (n + 1) ^ (c₀ + 1) with hP
      have hPc : (n + 1) ^ c₀ ≤ P := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
      have hP1 : n + 1 ≤ P := by
        calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
          _ ≤ P := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
      have hvP : v ≤ A₀ * P := by
        have h1 : m * (2 * (C₀ * (n + 1) ^ c₀) + 2) ≤ 2 * m * C₀ * P + 2 * m * P := by
          have := Nat.mul_le_mul_left (2 * m * C₀) hPc
          have h2 : 2 * m ≤ 2 * m * P := Nat.le_mul_of_pos_right _ (by omega)
          calc m * (2 * (C₀ * (n + 1) ^ c₀) + 2) = 2 * m * C₀ * (n + 1) ^ c₀ + 2 * m := by ring
            _ ≤ 2 * m * C₀ * P + 2 * m * P := by omega
        have e : A₀ * P = 2 * P + 2 * m * C₀ * P + 2 * m * P := by simp only [hA₀]; ring
        rw [e]
        omega
      have hpow : v ^ e j ≤ A₀ ^ e j * (n + 1) ^ E := by
        calc v ^ e j ≤ (A₀ * P) ^ e j := Nat.pow_le_pow_left hvP _
          _ = A₀ ^ e j * (n + 1) ^ ((c₀ + 1) * e j) := by rw [mul_pow, hP, ← pow_mul]
          _ ≤ A₀ ^ e j * (n + 1) ^ E :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (hejE j))
      have hone : 1 ≤ (n + 1) ^ E := Nat.one_le_pow _ _ (Nat.succ_pos n)
      have hcj : c j * (A₀ ^ e j + 1) ≤ Cc := by
        have := Finset.single_le_sum (f := fun j => c j * (A₀ ^ e j + 1))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        beta_reduce at this
        simp only [hCc]; omega
      calc c j * (v ^ e j + 1) ≤ c j * (A₀ ^ e j * (n + 1) ^ E + (n + 1) ^ E) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = c j * (A₀ ^ e j + 1) * (n + 1) ^ E := by ring
        _ ≤ Cc * (n + 1) ^ E := Nat.mul_le_mul_right _ hcj
  exact Set.mem_iUnion.mpr ⟨E, NSPACE.mono_const (a := 2 ^ E) (fun n => succ_pow_le n E) hsub⟩

/-- **Polynomially wide registers with logspace subroutines give `NPSPACE`**: the form of
`narm_decides_npspace` with deciders in `L`. Infrastructure for [AB09, §4.1].

**Proof sketch.** `L ⊆ PSPACE`, as `logSpace n ≤ n + 1`. -/
theorem narm_decides_npspace_of_logspace {L : Language Bool} [Fintype Λ] [DecidableEq Λ]
    (A : NARM m d Λ) (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE)
    (C₀ c₀ : ℕ)
    (hcorr : ∀ x, ∃ N,
      NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧
          ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ C₀ * (x.length + 1) ^ c₀)
        (some l₀, fun _ => 0, none) N ∧
      (x ∈ L ↔ NAns A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N true)) :
    L ∈ NPSPACE :=
  narm_decides_npspace A l₀ As (fun j => LOGSPACE_subset_PSPACE (hAs j)) C₀ c₀ hcorr

end Complexity.LogProg
