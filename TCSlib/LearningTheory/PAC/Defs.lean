/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Samples

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PAC learning over a finite domain

Probably approximately correct (PAC) learning in the realizable setting, information-theoretic
(learners are arbitrary functions, with finite random coins): a concept class `C : I → X → Bool`
over a finite domain `X`, the error of a hypothesis under a distribution, labelled samples of `m`
independent examples, and PAC, weak and fixed-distribution learning.

**Conventions.**
- A concept is a function `X → Bool`, and the class is indexed, `C : I → X → Bool`, as in
  [PS10, §8.1] (`{C_i}_{i ∈ I}`).
- A learner with `m` examples and coins `ρ` is a function
  `L : (Fin m → X × Bool) → ρ → (X → Bool)`; its coins are uniform on the finite type `ρ`.
- Distributions are `InformationTheory.FinDist`: real-valued, on a finite type.

**Deviations from [KV94, §1.2] and [SSBD14, Def 3.1].**
- **Fixed parameters.** `PACLearns C m L ε δ` fixes the sample size `m`, the accuracy `ε` and
  the confidence `δ`. The sources ask for one algorithm that works for all `ε, δ`, with a sample
  size polynomial in `1/ε`, `1/δ` (and, in [KV94], in the instance size), and efficiency is part
  of [KV94]'s definition. Here `PACLearnable C m ε δ` asks only for some learner at the given
  parameters. That notion is weaker, so impossibility results stated with it are stronger.
  Efficiency is layer 2's (the cryptographic statement of [PS10, Thm 179.1]).
- **Finite domains.** `X` is a finite type, so the "instance size" of [KV94] is not modelled.
  With `X` empty there is no distribution on `X`, so every PAC statement holds vacuously.

## Main definitions

* `PAC.err D h c`: the error `Pr_{x ← D}[h x ≠ c x]` of `h` against the target `c`.
* `PAC.label c s`: the sample `s` labelled by `c`.
* `PAC.accuracyProb D c m L ε`: the probability, over `m` examples from `D` and the coins, that
  the learner's hypothesis has error at most `ε`.
* `PAC.PACLearnsUnder D C m L ε δ`, `PAC.PACLearns C m L ε δ`: PAC learning under a fixed
  distribution and under every distribution.
* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: weak learning, accuracy `½ − γ` [KV94, §4].
* `PAC.PACLearnable C m ε δ`: some learner PAC-learns `C` at these parameters.

## Main results

* `PAC.err_nonneg`, `PAC.err_le_one`, `PAC.err_self`, `PAC.err_not`: basic properties; `err_not`
  says the complementary hypothesis has the complementary error.
* `PAC.pacLearns_const`: a class with one concept is PAC-learnable from no examples
  (non-vacuity).
* `PAC.not_pacLearnsUnder_of_neg`: no learner reaches a negative accuracy with confidence
  `δ < 1` (the definition does not hold trivially).

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2 (PAC learning) and §4 (weak learning).
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, ch. 3 (Definition 3.1).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
-/

namespace TCSlib.LearningTheory.PAC

open TCSlib.InformationTheory Finset

variable {X I ρ : Type*} [Fintype X]

/-! ### Error and samples -/

/-- The **error** of the hypothesis `h` against the target concept `c` under `D`:
`err_D(h, c) = Pr_{x ← D}[h x ≠ c x]` [KV94, §1.2]. -/
noncomputable def err (D : FinDist X) (h c : X → Bool) : ℝ := D.probTrue fun x => h x != c x

/-- The error is the probability of disagreement: `err_D(h, c) = Pr_{x ← D}[h x ≠ c x]`. -/
theorem err_eq (D : FinDist X) (h c : X → Bool) :
    err D h c = D.probTrue (fun x => h x != c x) := rfl

/-- The error is nonnegative. -/
theorem err_nonneg (D : FinDist X) (h c : X → Bool) : 0 ≤ err D h c := by
  rw [err_eq, FinDist.probTrue_eq]
  exact Finset.sum_nonneg fun x _ => D.nonneg x

/-- The error is at most `1`. -/
theorem err_le_one (D : FinDist X) (h c : X → Bool) : err D h c ≤ 1 := by
  rw [err_eq, FinDist.probTrue_eq, ← D.sum_prob]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun x _ _ => D.nonneg x

/-- The target has error `0` against itself. -/
theorem err_self (D : FinDist X) (c : X → Bool) : err D c c = 0 := by
  rw [err_eq, FinDist.probTrue_eq]
  simp

/-- The complementary hypothesis has the complementary error:
`err_D(¬h, c) = 1 − err_D(h, c)`. -/
theorem err_not (D : FinDist X) (h c : X → Bool) :
    err D (fun x => !h x) c = 1 - err D h c := by
  rw [err_eq, err_eq, ← FinDist.probTrue_not]
  congr 1
  funext x
  cases h x <;> cases c x <;> rfl

/-- The **labelled sample** `((x_j, c(x_j)))_j` of the examples `s` under the target `c`. -/
def label (c : X → Bool) {m : ℕ} (s : Fin m → X) : Fin m → X × Bool := fun j => (s j, c (s j))

omit [Fintype X] in
/-- The `j`-th labelled example is `(s j, c (s j))`. -/
theorem label_apply (c : X → Bool) {m : ℕ} (s : Fin m → X) (j : Fin m) :
    label c s j = (s j, c (s j)) := rfl

/-! ### PAC learning -/

variable [Fintype ρ] [Nonempty ρ]

/-- The **accuracy probability** of the learner `L` with `m` examples: over `m` independent
examples from `D`, labelled by the target `c`, and uniform coins, the probability that the
hypothesis has error at most `ε`. -/
noncomputable def accuracyProb (D : FinDist X) (c : X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) : ℝ :=
  ((D.iid m).prod (FinDist.uniform ρ)).probTrue
    fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)

/-- The accuracy probability as a probability over the examples and the coins. -/
theorem accuracyProb_eq (D : FinDist X) (c : X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) :
    accuracyProb D c m L ε = ((D.iid m).prod (FinDist.uniform ρ)).probTrue
      (fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)) := rfl

/-- **PAC learning under the distribution `D`** (fixed-distribution learning): for every concept
of the class, with probability at least `1 − δ` the hypothesis has error at most `ε`. -/
def PACLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) : Prop :=
  ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε

/-- `PACLearnsUnder` unfolded. -/
theorem pacLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
    PACLearnsUnder D C m L ε δ ↔ ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε := Iff.rfl

/-- **PAC learning** [KV94, §1.2], [SSBD14, Def 3.1], at fixed `m`, `ε`, `δ`: for every
distribution `D` on `X` and every concept `C i`, with probability at least `1 − δ` over `m`
examples from `D` labelled by `C i` and the learner's coins, the hypothesis has error at most `ε`
under `D`. -/
def PACLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
    Prop :=
  ∀ D : FinDist X, PACLearnsUnder D C m L ε δ

/-- `PACLearns` unfolded. -/
theorem pacLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
    (ε δ : ℝ) : PACLearns C m L ε δ ↔ ∀ D, PACLearnsUnder D C m L ε δ := Iff.rfl

/-- **Weak learning under `D`** [KV94, §4]: PAC learning under `D` with accuracy `½ − γ`, a
hypothesis better than a fair coin by `γ`. -/
def WeakLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) : Prop :=
  PACLearnsUnder D C m L (1 / 2 - γ) δ

/-- `WeakLearnsUnder` unfolded. -/
theorem weakLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
    WeakLearnsUnder D C m L γ δ ↔ PACLearnsUnder D C m L (1 / 2 - γ) δ := Iff.rfl

/-- **Weak learning** [KV94, §4]: under every distribution, accuracy `½ − γ`. -/
def WeakLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
    Prop :=
  ∀ D : FinDist X, WeakLearnsUnder D C m L γ δ

/-- `WeakLearns` unfolded. -/
theorem weakLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
    (γ δ : ℝ) : WeakLearns C m L γ δ ↔ ∀ D, WeakLearnsUnder D C m L γ δ := Iff.rfl

omit [Fintype ρ] [Nonempty ρ] in
/-- **PAC-learnability at fixed parameters**: some learner, with finite nonempty coins, learns `C`
from `m` examples with accuracy `ε` and confidence `δ`. -/
def PACLearnable (C : I → X → Bool) (m : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (ρ' : Type) (_ : Fintype ρ') (_ : Nonempty ρ') (L : (Fin m → X × Bool) → ρ' → X → Bool),
    PACLearns C m L ε δ

omit [Fintype ρ] [Nonempty ρ] in
/-- `PACLearnable` unfolded. -/
theorem pacLearnable_iff (C : I → X → Bool) (m : ℕ) (ε δ : ℝ) :
    PACLearnable C m ε δ ↔
      ∃ (ρ' : Type) (_ : Fintype ρ') (_ : Nonempty ρ')
        (L : (Fin m → X × Bool) → ρ' → X → Bool), PACLearns C m L ε δ := Iff.rfl

/-! ### Non-vacuity -/

/-- **A class with one concept is PAC-learnable from no examples** (non-vacuity of
`PACLearns`): if every `C i` is `c₀`, the learner that outputs `c₀` has error `0`, so it learns
at every accuracy `ε ≥ 0` and confidence `δ ≥ 0`. -/
theorem pacLearns_const {C : I → X → Bool} {c₀ : X → Bool} (hC : ∀ i, C i = c₀) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    PACLearns C 0 (fun (_ : Fin 0 → X × Bool) (_ : ρ) => c₀) ε δ := by
  intro D i
  rw [accuracyProb_eq, hC i]
  have h : (fun sr : (Fin 0 → X) × ρ =>
      decide (err D ((fun (_ : Fin 0 → X × Bool) (_ : ρ) => c₀) (label c₀ sr.1) sr.2) c₀ ≤ ε)) =
      fun _ => true := by
    funext sr
    simp only [err_self, hε, decide_true]
  rw [h, FinDist.probTrue_true]
  linarith

/-- **No learner reaches a negative accuracy with confidence `δ < 1`**: the error is
nonnegative, so the accuracy event is empty and its probability `0 < 1 − δ`. `PACLearns` is
therefore not trivially satisfied. -/
theorem not_pacLearnsUnder_of_neg (D : FinDist X) {C : I → X → Bool} [Nonempty I] {m : ℕ}
    (L : (Fin m → X × Bool) → ρ → X → Bool) {ε δ : ℝ} (hε : ε < 0) (hδ : δ < 1) :
    ¬ PACLearnsUnder D C m L ε δ := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 := h i
  rw [accuracyProb_eq] at h1
  have h0 : (fun sr : (Fin m → X) × ρ => decide (err D (L (label (C i) sr.1) sr.2) (C i) ≤ ε)) =
      fun _ => false := by
    funext sr
    have := err_nonneg D (L (label (C i) sr.1) sr.2) (C i)
    simp only [decide_eq_false_iff_not, not_le]
    linarith
  rw [h0, FinDist.probTrue_eq] at h1
  simp at h1
  linarith

end TCSlib.LearningTheory.PAC
