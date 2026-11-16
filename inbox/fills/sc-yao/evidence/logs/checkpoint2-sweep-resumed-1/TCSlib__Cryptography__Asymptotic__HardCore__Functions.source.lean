/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.NextBit
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.Asymptotic.HardCoreGL
import TCSlib.Cryptography.Asymptotic.HardCoreCollection
import TCSlib.Cryptography.Asymptotic.HardCoreGLFamily
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin
import TCSlib.Cryptography.HardcoreBit.ThreeQuarters
import TCSlib.Cryptography.OneWayFunctions.OutputLength

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core predicates and Goldreich–Levin for function families

The hard-core predicate of [PS10, Definition 78.3] combines efficient evaluation
with the hardness of predicting its bit from a function image. Goldreich–Levin
[PS10, Theorem 87.3] constructs a one-way family `g(x, r) = (f(x), r)` with the
hard-core bit `⟨x, r⟩`. The typed-family experiments use the finite reductions
of [Gar26, §2.5] and the polynomial-time machines in `Asymptotic.HardCoreLemmas`
and `Asymptotic.HardCoreGLFamily`.

**Deviation.** The prediction experiment uses the same parameter for the
domain and the adversary. The predictor returns the string `[true]` to signal
a true prediction. The inner product is hard-core for the padded family
`g` (source error 26).

## Main definitions

* `TCSlib.Cryptography.HardCore` and `TCSlib.Cryptography.PermFamily.HardCore`
  give the function and permutation forms of the hard-core predicate.
* `TCSlib.Cryptography.FunFamily.glPad`, `TCSlib.Cryptography.FunFamily.glBit`
  and `TCSlib.Cryptography.FunFamily.glInverter` give the padded family, its
  inner-product predicate and its inverter.

## Main results

* `TCSlib.Cryptography.hardCore_iff` and `TCSlib.Cryptography.PermFamily.hardCore_iff`
  characterize hard-core predicates. `TCSlib.Cryptography.not_hardCore_const`
  excludes constant predicates.
* `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad` proves one-wayness.
  `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore` proves hardness of
  the inner product. `TCSlib.Cryptography.goldreich_levin` combines the two.

The concrete claims have their own proofs in `Asymptotic.HardCoreClaims`.
The collection version used in [PS10, Theorem 104.4] is in
`Asymptotic.HardCoreCollection`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.3.3 and §§3.4.2–3.4.3.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figures 2.3–2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Hard-core predicates [PS10, Definition 78.3] -/

/-- `h` is a **hard-core predicate** for the family `f` [PS10, Definition 78.3]: `h n x` is
computable in deterministic polynomial time from `⟨1^n, x⟩`, and for every non-uniform PPT
`A` there is a negligible `ε` with `Pr[x ← {0,1}^{inLen n} : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)`
for all `n` (the experiment is the concrete `predProb` of [Gar26, Definition 2.3]).

**Deviation:** the text mixes `k` and `n` (`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`, `∀ k`); here
`k = n` (source error 30); `h` is a typed family on `{0,1}^{inLen n}` (D5); the efficiency
clause is a deterministic evaluator on `⟨1^n, x⟩` (as `FunFamily.Easy`, Deviation 3); the
predictor's verdict is the string `[true]` (Deviation 4). -/
def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=
  (∃ H : List Bool → List Bool, PolyTimeComputable H ∧
    ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n

/-- **Hard-core unfolded** [PS10, Definition 78.3]: `h` is hard-core for `f` iff some
polynomial-time `H` computes `[h n x]` from `⟨1^n, x⟩`, and for every non-uniform PPT `A` some
negligible `ε` bounds `Pr[x ← {0,1}^{inLen n} : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)` for all `n`. -/
theorem hardCore_iff (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) :
    HardCore 𝓕 h ↔
      (∃ H : List Bool → List Bool, PolyTimeComputable H ∧
        ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
      ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n :=
  Iff.rfl

/-- The efficiency clause of a hard-core predicate [PS10, Definition 78.3 (1)]. -/
theorem HardCore.easy {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
    (hh : HardCore 𝓕 h) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x] := hh.1

/-- The unpredictability clause of a hard-core predicate [PS10, Definition 78.3 (2)]. -/
theorem HardCore.hard {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
    (hh : HardCore 𝓕 h) (A : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n := hh.2 A

/-- `h : ∀ n, {0,1}^n → Bool` is a **hard-core predicate for the permutation family `P`**
[PS10, Definition 78.3, for the permutations of Theorems 79.4, 87.3 and 126.4]: `h` is hard-core
for `P.toFunFamily`, read on `{0,1}^{inLen n}` through the domain equivalence
`P.toFunFamily_domEquiv n : {0,1}^{inLen n} ≃ {0,1}^n`. -/
def PermFamily.HardCore (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  TCSlib.Cryptography.HardCore P.toFunFamily fun n x => h n (P.toFunFamily_domEquiv n x)

/-- The defining equivalence of `PermFamily.HardCore`:
`P.HardCore h ↔ HardCore P.toFunFamily (h ∘ domEquiv)`. -/
theorem PermFamily.hardCore_iff (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) :
    P.HardCore h ↔
      TCSlib.Cryptography.HardCore P.toFunFamily fun n x => h n (P.toFunFamily_domEquiv n x) :=
  Iff.rfl

/-- **The prediction experiment of `P.toFunFamily` is that of the permutation**: predicting
`h ∘ domEquiv` from `P.toFunFamily.f n` with `A.predictor n (outLen n)` has the probability of
predicting `h n` from `P.f n` with `A.predictor n n`. -/
theorem PermFamily.predProb_toFunFamily (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (A : NUPPT) (n : ℕ) :
    predProb (P.toFunFamily.f n) (fun x => h n (P.toFunFamily_domEquiv n x))
        (A.predictor n (P.toFunFamily.outLen.eval n)) =
      predProb (P.f n) (h n) (A.predictor n n) := by
  rw [predProb_def, predProb_def]
  refine uprob_eq_of_equiv ((P.toFunFamily_domEquiv n).prodCongr (Equiv.refl _)) fun z => ?_
  obtain ⟨x, r⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq, NUPPT.predictor_eq,
      NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq,
    NUPPT.distinguisher_eq]
  rw [← P.toFunFamily_codEquiv_ofFn, P.toFunFamily_f_domEquiv]

/-- The efficiency clause for a permutation family [PS10, Definition 78.3 (1)]: some
polynomial-time `H` computes `[h n x]` from `⟨1^n, x⟩` for `x ∈ {0,1}^n`. -/
theorem PermFamily.HardCore.easy {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hh : P.HardCore h) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x] := by
  obtain ⟨H, hH, hHx⟩ := TCSlib.Cryptography.HardCore.easy ((P.hardCore_iff h).1 hh)
  refine ⟨H, hH, fun n x => ?_⟩
  have hx := hHx n ((P.toFunFamily_domEquiv n).symm x)
  rwa [P.toFunFamily_domEquiv_symm_ofFn, Equiv.apply_symm_apply] at hx

/-- The unpredictability clause for a permutation family [PS10, Definition 78.3 (2)]: for every
non-uniform PPT `A` some negligible `ε` bounds
`Pr[x ← {0,1}^n : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)` for all `n`. -/
theorem PermFamily.HardCore.hard {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hh : P.HardCore h) (A : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, predProb (P.f n) (h n) (A.predictor n n) ≤ 1 / 2 + ε n := by
  obtain ⟨ε, hε, hb⟩ := TCSlib.Cryptography.HardCore.hard ((P.hardCore_iff h).1 hh) A
  exact ⟨ε, hε, fun n => (P.predProb_toFunFamily h A n).symm.trans_le (hb n)⟩

/-- **Hard-core for a permutation family, from the two clauses** [PS10, Definition 78.3]:
an evaluator of `[h n x]` on `⟨1^n, x⟩` and, for every non-uniform PPT `A`, a negligible `ε`
with `Pr[x ← {0,1}^n : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)`. -/
theorem PermFamily.HardCore.of_easy_hard {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (he : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x])
    (hA : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, predProb (P.f n) (h n) (A.predictor n n) ≤ 1 / 2 + ε n) :
    P.HardCore h := by
  refine (P.hardCore_iff h).2 ((hardCore_iff _ _).2 ⟨?_, fun A => ?_⟩)
  · obtain ⟨H, hH, hHx⟩ := he
    refine ⟨H, hH, fun n x => ?_⟩
    rw [← P.toFunFamily_domEquiv_ofFn n x]
    exact hHx n _
  · obtain ⟨ε, hε, hb⟩ := hA A
    exact ⟨ε, hε, fun n => (P.predProb_toFunFamily h A n).trans_le (hb n)⟩

/-- **A constant predicate is never hard-core** (non-vacuity of the hardness clause of
[PS10, Definition 78.3]): the machine that ignores its input and outputs `[b]` predicts
`h ≡ b` with probability one at every `n`, and `1 ≤ 1/2 + ε(n)` contradicts negligibility.

**Proof sketch.** Take `A := ofPolyTimeUniform (const [b])`; `A.predictor n m y r = b` for
all `y, r` (`NUPPT.output_ofPolyTime`), so `predProb = 1` (`uprob_eq_one_of_forall`); then
`1/2 ≤ ε n` for every `n`, while `|ε n| < 1/n` for large `n`. -/
theorem not_hardCore_const (𝓕 : FunFamily) (b : Bool) : ¬ HardCore 𝓕 (fun _ _ => b) := by
  rintro ⟨-, hA⟩
  obtain ⟨ε, hε, h⟩ := hA (NUPPT.ofPolyTimeUniform (polyTimeComputable_const [b]) (.const 0))
  have hone : ∀ n, predProb (𝓕.f n) (fun _ => b)
      ((NUPPT.ofPolyTimeUniform (polyTimeComputable_const [b]) (.const 0)).predictor n
        (𝓕.outLen.eval n)) = 1 := by
    intro n
    haveI : Nonempty ((Fin (𝓕.inLen.eval n) → Bool) ×
      (NUPPT.ofPolyTimeUniform (polyTimeComputable_const [b]) (.const 0)).Coins n) :=
      ⟨(fun _ => false, fun _ => false)⟩
    refine HardcoreBit.uprob_eq_one_of_forall fun z => ?_
    simp only [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
        NUPPT.runAtL_eq, NUPPT.output_ofPolyTimeUniform]
    cases b <;> simp
  obtain ⟨n₀, hn₀⟩ := (negligible_iff ε).1 hε 1
  have h1 := h (max n₀ 2)
  rw [hone] at h1
  have h2 := hn₀ (max n₀ 2) (le_max_left _ _)
  have h3 : (2 : ℝ) ≤ max n₀ 2 := by exact_mod_cast le_max_right n₀ 2
  have h4 : 1 / ((max n₀ 2 : ℕ) : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]
    exact one_div_le_one_div_of_le (by norm_num) h3
  linarith [le_abs_self (ε (max n₀ 2))]

/-! ## Goldreich–Levin for function families [PS10, Theorem 87.3] -/

namespace FunFamily

variable (𝓕 : FunFamily)

/-- The function `g(x, r) = (f(x), r)` of [PS10, Theorem 87.3] (`|x| = |r| = inLen n`) as a
family: input length `2·inLen`, output length `outLen + inLen`, the string `x ‖ r` split by
`Fin.appendEquiv` and `g` the concrete `HardcoreBit.glPad (f n)` [Gar26, Theorem 2.3]. -/
def glPad : FunFamily where
  inLen := .add 𝓕.inLen 𝓕.inLen
  outLen := .add 𝓕.outLen 𝓕.inLen
  f n z := Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
    (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z))

/-- The predicate `h(x, r) = ⟨x, r⟩` of [PS10, Theorem 87.3] on the string `x ‖ r`
(the concrete `HardcoreBit.glBit`, Fact 88.4's inner product). -/
def glBit : ∀ n, (Fin (𝓕.glPad.inLen.eval n) → Bool) → Bool :=
  fun n z => HardcoreBit.glBit ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)

/-- The inverter of `g` built from a recovery procedure `R` for `x` from `f(x)`: on
`f(x) ‖ r` with coins `c` it outputs `R(f(x), c) ‖ r` (the concrete `HardcoreBit.glInverter`;
all inverters of [PS10, §3.4.3] have this shape). -/
def glInverter {γ : Type*} (n : ℕ) (R : (Fin (𝓕.outLen.eval n) → Bool) → γ → Fin (𝓕.inLen.eval n) → Bool) :
    (Fin (𝓕.glPad.outLen.eval n) → Bool) → γ → (Fin (𝓕.glPad.inLen.eval n) → Bool) :=
  fun y c => Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)
    (HardcoreBit.glInverter R ((Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).symm y) c)

/-- The input length of `g`: `inLen_g(n) = inLen(n) + inLen(n)`. -/
theorem glPad_inLen_eval (n : ℕ) : 𝓕.glPad.inLen.eval n = 𝓕.inLen.eval n + 𝓕.inLen.eval n := rfl

/-- The output length of `g`: `outLen_g(n) = outLen(n) + inLen(n)`. -/
theorem glPad_outLen_eval (n : ℕ) :
    𝓕.glPad.outLen.eval n = 𝓕.outLen.eval n + 𝓕.inLen.eval n := rfl

/-- **The inputs of `g` are strings `x ‖ r`**: the published equivalence
`{0,1}^{inLen_g(n)} ≃ {0,1}^{inLen(n) + inLen(n)}` (the identity on the definition). -/
def glPad_inEquiv (n : ℕ) :
    (Fin (𝓕.glPad.inLen.eval n) → Bool) ≃ (Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool) :=
  Equiv.refl _

/-- **The outputs of `g` are strings `y ‖ r`**: the published equivalence
`{0,1}^{outLen_g(n)} ≃ {0,1}^{outLen(n) + inLen(n)}` (the identity on the definition). -/
def glPad_outEquiv (n : ℕ) :
    (Fin (𝓕.glPad.outLen.eval n) → Bool) ≃ (Fin (𝓕.outLen.eval n + 𝓕.inLen.eval n) → Bool) :=
  Equiv.refl _

/-- The input equivalence keeps the string: `List.ofFn (glPad_inEquiv n z) = List.ofFn z`. -/
theorem glPad_inEquiv_ofFn (n : ℕ) (z : Fin (𝓕.glPad.inLen.eval n) → Bool) :
    List.ofFn (𝓕.glPad_inEquiv n z) = List.ofFn z := rfl

/-- The inverse input equivalence keeps the string. -/
theorem glPad_inEquiv_symm_ofFn (n : ℕ) (z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool) :
    List.ofFn ((𝓕.glPad_inEquiv n).symm z) = List.ofFn z := rfl

/-- The output equivalence keeps the string: `List.ofFn (glPad_outEquiv n y) = List.ofFn y`. -/
theorem glPad_outEquiv_ofFn (n : ℕ) (y : Fin (𝓕.glPad.outLen.eval n) → Bool) :
    List.ofFn (𝓕.glPad_outEquiv n y) = List.ofFn y := rfl

/-- The inverse output equivalence keeps the string. -/
theorem glPad_outEquiv_symm_ofFn (n : ℕ) (y : Fin (𝓕.outLen.eval n + 𝓕.inLen.eval n) → Bool) :
    List.ofFn ((𝓕.glPad_outEquiv n).symm y) = List.ofFn y := rfl

/-- Unfolding: `g` on `x ‖ r` is `f(x) ‖ r`. -/
theorem glPad_f (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glPad.f n (Fin.append x r) = Fin.append (𝓕.f n x) r := by
  show Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n)
    ((Fin.appendEquiv _ _).symm (Fin.appendEquiv _ _ (x, r)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Unfolding: `h(x ‖ r) = ⟨x, r⟩`. -/
theorem glBit_append (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glBit n (Fin.append x r) = HardcoreBit.ip x r := by
  show HardcoreBit.glBit ((Fin.appendEquiv _ _).symm (Fin.appendEquiv _ _ (x, r))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- `g` through the published equivalences: `g(x ‖ r) = f(x) ‖ r` with `x ‖ r` read by
`glPad_inEquiv` and the value by `glPad_outEquiv`. -/
theorem glPad_f_equiv (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glPad_outEquiv n (𝓕.glPad.f n ((𝓕.glPad_inEquiv n).symm (Fin.append x r))) =
      Fin.append (𝓕.f n x) r :=
  𝓕.glPad_f n x r

/-- `h` through the published equivalence: `h(x ‖ r) = ⟨x, r⟩`. -/
theorem glBit_equiv (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glBit n ((𝓕.glPad_inEquiv n).symm (Fin.append x r)) = HardcoreBit.ip x r :=
  𝓕.glBit_append n x r

/-- **Bridge to the concrete setting (prediction)**: the prediction probability of `A` for
`h = ⟨x, r⟩` of the family `g` equals that of `A ∘ (append)` for `glBit` of the concrete
`HardcoreBit.glPad (f n)` [Gar26, Theorem 2.3]. -/
theorem predProb_glPad {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) :
    predProb (𝓕.glPad.f n) (𝓕.glBit n) A =
      predProb (HardcoreBit.glPad (𝓕.f n)) HardcoreBit.glBit
        (fun y r => A ((𝓕.glPad_outEquiv n).symm
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) := by
  rw [predProb_def, predProb_def]
  exact uprob_eq_of_equiv
    ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm.prodCongr (Equiv.refl ρ))
    fun _ => Iff.rfl

/-- **Bridge to the concrete setting (inversion)**: the inversion probability of the family
inverter `glInverter n R` against the family `g` equals that of the concrete
`HardcoreBit.glInverter R` against `HardcoreBit.glPad (f n)`. -/
theorem invProb_glInverter {γ : Type*} [Fintype γ] (n : ℕ)
    (R : (Fin (𝓕.outLen.eval n) → Bool) → γ → Fin (𝓕.inLen.eval n) → Bool) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n R) =
      invProb (HardcoreBit.glPad (𝓕.f n)) (HardcoreBit.glInverter R) := by
  simp only [invProb_def]
  refine uprob_eq_of_equiv (splitPair (𝓕.inLen.eval n) (𝓕.inLen.eval n) γ) fun z => ?_
  simp only [glPad, glInverter, splitPair_apply, splitPair_symm_apply, Equiv.coe_fn_mk,
      Equiv.symm_apply_apply]
  exact Equiv.apply_eq_iff_eq _

/-- **`g` is a permutation when `f` is** ([PS10, Theorem 87.3], the "(OWP)" clause): the
family `g(x, r) = (f(x), r)` is bijective at every `n` at which `f` is.

Note (run-3 audit P4-1): bijectivity of a `FunFamily` of input length `var + var` (even
lengths only) does not make `𝓕.glPad` a `PermFamily`; that form is `PermFamily.glHalf` /
`OneWayPermutation.glHalf` (`Asymptotic/HardCorePermutation/GoldreichLevin.lean`,
`glHalf_f_even`). -/
theorem glPad_f_bijective (n : ℕ) (hf : Function.Bijective (𝓕.f n)) :
    Function.Bijective (𝓕.glPad.f n) := by
  have e : HardcoreBit.glPad (𝓕.f n) =
      ⇑((Equiv.ofBijective _ hf).prodCongr (Equiv.refl (Fin (𝓕.inLen.eval n) → Bool))) := by
    funext z; rfl
  show Function.Bijective fun z => Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n)
    ((Fin.appendEquiv _ _).symm z))
  rw [e]
  exact (Fin.appendEquiv _ _).bijective.comp
    (((Equiv.ofBijective _ hf).prodCongr _).bijective.comp (Fin.appendEquiv _ _).symm.bijective)

/-- **`g` is one-way** ([PS10, Theorem 87.3], first clause; inventory Thm-87.3.a): if `f` is a
strong one-way function then so is `g(x, r) = (f(x), r)`.

**Proof sketch.** *Easy:* from `h.easy = ⟨F, hF, hFx⟩`, the evaluator on `⟨1^n, x ‖ r⟩` is
`F ⟨1^n, (take (inLen n))⟩ ++ drop (inLen n)` (`polyTimeComputable_pairTakePoly 𝓕.inLen`,
`pairDropPoly`, `PolyTimeComputable.append`; `List.ofFn_fin_append`). *Hard:* for an inverter
`A : NUPPT` of `g`, the inverter `B` of `f`: coins `inLen + A.coins` (`NUPPT.exists_split
𝓕.inLen`: the first `inLen n` coins are the padding `r`), on `⟨1^n, y⟩` it calls `A` once on
`⟨1^n, y ++ r⟩` (`NUPPT.exists_seq`) and outputs the first `inLen n` bits of the answer
(`pairTakePoly 𝓕.inLen`; a wrong-length answer stays wrong). Concretely this is the padding
inverter `OneWay.padInverter` of [Gar26, Lemma 2.3] (`OneWay.pad f = HardcoreBit.glPad f`
definitionally): `𝓕.glPad.invProbAt A n ≤ 𝓕.invProbAt B n` by `invProbAt_eq_uprob`,
`uprob_comp_equiv` on the coin split `splitCoins`, `uprob_mono` (if `A`'s decoded answer
`x' ‖ r'` satisfies `f(x') ‖ r' = f(x) ‖ r` then `f(x') = f(x)`, `Fin.append` injective in
its first argument); then `Negligible.mono` with `h.hard B`. -/
theorem StrongOneWay.glPad {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.glPad.StrongOneWay := by
  obtain ⟨F, hF, hFx⟩ := (FunFamily.easy_iff 𝓕).1 h.easy
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := exists_glPadEvaluator 𝓕 hF hFx
    refine (FunFamily.easy_iff _).2 ⟨E, hE, fun n z => ?_⟩
    obtain ⟨⟨x, r⟩, rfl⟩ := (Fin.appendEquiv _ _).surjective z
    show E (NUPPT.advInput n (List.ofFn (Fin.append x r))) = List.ofFn (𝓕.glPad.f n (Fin.append x r))
    rw [List.ofFn_fin_append, hEs, glPad_f, List.ofFn_fin_append]
  · refine (h.hard (glPadInvMachine A 𝓕.inLen)).mono ⟨0, fun n _ => ?_⟩
    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
    exact invProbOpt_glPad_le 𝓕 A n

/-- **`⟨x, r⟩` is hard-core for `g`** ([PS10, Theorem 87.3], second clause; inventory
Thm-87.3.b): if `f` is a strong one-way function then `h(x, r) = ⟨x, r⟩` is a hard-core
predicate for `g(x, r) = (f(x), r)`.

**Deviation:** the text says hard-core "for `f`" (source error 26); the final constant of the
text is `ε³/(32n)` (with `ε' = ε/2`), the concrete layer's `invProb_guessInverter` gives
`ε/(4·2^k)` with `2n ≤ ε²(2^k − 1)` (source error 37; `[GL89]`).

**Proof sketch.** *Easy:* `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` is the inner-product evaluator `ipFun`
(the selective block XOR `selXorFun` with one-bit blocks, `Asymptotic/HardCoreLoops.lean`) on
the halves cut by `pairTakePoly 𝓕.inLen`/`pairDropPoly 𝓕.inLen` (`exists_glBitEvaluator`).
*Hard:* by contradiction. The hardness function is `ε n := max 0 (predProb − 1/2)`; if it is
not negligible, `not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ predProb (𝓕.glPad.f n)
(𝓕.glBit n) (A.predictor n _)` for infinitely many `n`. Put `ε_n := n^{−c}` and the hard-wired
`k(n) := size (2 m(n) n^{2c})` (`glK`), so that `2m ≤ ε_n²(2^{k(n)} − 1)` (`glK_real`) and
`2^{k(n)} ≤ 4 m(n) n^{2c} + 1` (`two_pow_glK_le`); `predProb_glPad` transfers the hypothesis to
the concrete setting and `HardcoreBit.invProb_guessInverter` gives `ε_n/(4·2^{k(n)}) ≤ invProb
(HardcoreBit.glPad (𝓕.f n)) (guessInverter A' k(n))` [PS10, Algorithm 89.6]. The inverter as
an `NUPPT` is `glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen …`
(`Asymptotic/HardCoreGL.lean`): advice `⟨⟨1^k, ⟨1^{2^k−1}, table⟩⟩, A.advice n⟩` where the
table lists the pairs `⟨e_i, β_L⟩` of all rounds, coins `K m + K + m K A.coins` (the `s_j`,
the `b_j`, one coin block of `A` per round, unread coins), and the voting loop `GLLoop`
(`polyTimeComputable_stateIterate`) that queries `A` on `⟨1^n, y ‖ (S_L ⊕ e_i)⟩` with
`S_L`, `B_L` from `selXorFun`/`ipFun` and takes the `m` majorities by
`polyTimeComputable_blockMap`/`polyTimeComputable_majority`. Its inversion probability is
exactly that of `guessInverter` (`invProbOpt_glFam_eq`, through the coin bijection
`glCoinsEquiv` and `glMachine_runAt_guessRecover`), so `𝓕.glPad.invProbAt B n ≥
n^{−c}/(4(4 m n^{2c} + 1)) ≥ n^{−(c+d+1)}` infinitely often (`PolyExpr.eval_le`),
contradicting `(StrongOneWay.glPad h).hard B`. -/
theorem StrongOneWay.glPad_hardCore {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    HardCore 𝓕.glPad 𝓕.glBit := by
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨H, hH, hHx⟩ := exists_glBitEvaluator 𝓕.inLen
    refine ⟨H, hH, fun n z => ?_⟩
    obtain ⟨⟨x, r⟩, rfl⟩ := (Fin.appendEquiv _ _).surjective z
    show H (NUPPT.advInput n (List.ofFn (Fin.append x r))) = [𝓕.glBit n (Fin.append x r)]
    rw [List.ofFn_fin_append, hHx, glBit_append]
  · refine ⟨fun n => max 0 (predProb (𝓕.glPad.f n) (𝓕.glBit n)
      (A.predictor n (𝓕.glPad.outLen.eval n)) - 1 / 2), ?_, fun n => by
        linarith [le_max_right (0 : ℝ)
          (predProb (𝓕.glPad.f n) (𝓕.glBit n) (A.predictor n (𝓕.glPad.outLen.eval n)) - 1 / 2)]⟩
    by_contra hneg
    obtain ⟨c, hc⟩ := not_negligible_iff.mp hneg
    set K := glKBound 𝓕.inLen c with hK
    set B := glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen K (glK 𝓕.inLen c)
      (two_pow_glK_le 𝓕.inLen c) with hB
    have hBneg := (h.glPad).hard B
    obtain ⟨C, d, hCd⟩ := K.eval_le
    obtain ⟨n₀, hn₀⟩ := (negligible_iff _).1 hBneg (c + d + 1)
    obtain ⟨n, hn, hgap⟩ := hc (max n₀ (max 1 (4 * C * 2 ^ d)))
    have hn1 : 1 ≤ n := le_of_max_le_left (le_of_max_le_right hn)
    have hnC : 4 * C * 2 ^ d ≤ n := le_of_max_le_right (le_of_max_le_right hn)
    have hε : (0 : ℝ) < 1 / (n : ℝ) ^ c := by positivity
    have hpred : 1 / 2 + 1 / (n : ℝ) ^ c ≤
        predProb (𝓕.glPad.f n) (𝓕.glBit n) (A.predictor n (𝓕.glPad.outLen.eval n)) := by
      rw [abs_of_nonneg (le_max_left _ _)] at hgap
      rcases le_or_gt (predProb (𝓕.glPad.f n) (𝓕.glBit n)
        (A.predictor n (𝓕.glPad.outLen.eval n)) - 1 / 2) 0 with hle | hlt
      · rw [max_eq_left hle] at hgap; linarith
      · rw [max_eq_right hlt.le] at hgap; linarith
    rw [predProb_glPad] at hpred
    have hGL := HardcoreBit.invProb_guessInverter (𝓕.f n)
      (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
        (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c)
      hε (glK_real 𝓕.inLen c n hn1) hpred
    have hid : 𝓕.glPad.invProbAt B n = invProb (HardcoreBit.glPad (𝓕.f n))
        (HardcoreBit.guessInverter (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) (glK 𝓕.inLen c n)) :=
      invProbOpt_glFam_eq 𝓕 A K (glK 𝓕.inLen c) (two_pow_glK_le 𝓕.inLen c) n
        (glK_pos_or 𝓕.inLen c n hn1)
    have hsmall := hn₀ n (le_of_max_le_left hn)
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), hid] at hsmall
    have h2k : ((2 : ℝ) ^ glK 𝓕.inLen c n) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ d := by
      exact_mod_cast (two_pow_glK_le 𝓕.inLen c n).trans (hCd n)
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnCR : (4 : ℝ) * C * 2 ^ d ≤ n := by exact_mod_cast hnC
    have hpow : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hlow : 1 / (n : ℝ) ^ (c + d + 1) ≤ 1 / (n : ℝ) ^ c / (4 * 2 ^ glK 𝓕.inLen c n) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      calc (n : ℝ) ^ c * (4 * 2 ^ glK 𝓕.inLen c n)
          ≤ (n : ℝ) ^ c * (4 * (C * (2 * (n : ℝ)) ^ d)) := by
            gcongr
            exact h2k.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
        _ = (n : ℝ) ^ c * (n : ℝ) ^ d * (4 * C * 2 ^ d) := by ring
        _ ≤ (n : ℝ) ^ c * (n : ℝ) ^ d * n := by gcongr
        _ = (n : ℝ) ^ (c + d + 1) := by ring
    linarith

end FunFamily

/-- **Goldreich–Levin** [PS10, Theorem 87.3; GL89]: if `f` is a strong one-way function then
`g(x, r) = (f(x), r)` is a strong one-way function and `h(x, r) = ⟨x, r⟩` is a hard-core
predicate for `g` (bijectivity of `g` at each `n` is `FunFamily.glPad_f_bijective`).

**Deviation:** hard-core for `g`, not "for `f`" (source error 26).

Repair (run-3 audit P4-1): statement unchanged. The text's "(OWP)" reading — "the existence
of OWPs implies the existence of OWPs with a hard-core bit" (p. 86), i.e. a `PermFamily` with
a `HardCore` predicate feeding `owp_hardcore_prg`, `cor_81_7` and `Commitment.owp_commitment` —
is **not** derivable from this theorem: `𝓕.glPad` has input length `var + var` and is never a
`PermFamily`. That route is `OneWayPermutation.glHalf`
(`Asymptotic/HardCorePermutation/GoldreichLevin.lean`):
the balanced permutation `PermFamily.glHalf`, `x ‖ w ↦ f_{⌊n/2⌋}(x) ‖ w`, whose one-wayness and
hard-core bit reduce to `StrongOneWay.glPad` and `StrongOneWay.glPad_hardCore` at parameter
`⌊n/2⌋` through `predProb_glHalf_even`/`predProb_glHalf_odd`, `invProb_glHalf_even`/
`invProb_glHalf_odd_le` and `Negligible.comp_div_two`. -/
theorem goldreich_levin {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    𝓕.glPad.StrongOneWay ∧ HardCore 𝓕.glPad 𝓕.glBit :=
  ⟨h.glPad, h.glPad_hardCore⟩

end TCSlib.Cryptography
