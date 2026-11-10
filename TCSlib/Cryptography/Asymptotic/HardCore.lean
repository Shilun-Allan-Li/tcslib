/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.NextBit
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
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Stretch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core predicates, generators from one-way permutations, Goldreich–Levin

The material of [PS10, §3.3.3–§3.3.5 and §3.4.2–§3.4.3]: hard-core predicates
[PS10, Definition 78.3]; the one-bit-stretch generator `G(s) = f(s) ‖ h(s)` from a one-way
permutation `f` with hard-core predicate `h` [PS10, Theorem 79.4]; the iterated generator
`h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` [PS10, Corollary 81.7]; and the Goldreich–Levin theorem:
for every one-way function `f`, `g(x, r) = (f(x), r)` is one-way and `⟨x, r⟩` is hard-core for
`g` [PS10, Theorem 87.3], together with the concrete claims of its proof (the oversimplified
case, the `3/4 + ε` case, the good set, Fact 88.4, Algorithms 88.5 and 89.6, the
pairwise-independence and union-bound claims, the final bound; in
`Asymptotic/HardCoreClaims.lean`) and the version for collections of (trapdoor) permutations
needed by [PS10, Theorem 104.4] (in `Asymptotic/HardCoreCollection.lean`, which this file
imports).

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer is
the frozen Garg development reused verbatim: `owpPredictor`/`exists_owpPredictor`
(`Pseudorandom/GeneratorFromPermutation.lean`), `prgExt`/`prgExtRed`/`exists_prgExtRed_ge`
(`Pseudorandom/Generators.lean`), `HardcoreBit.glPad`, `glBit`, `guessInverter`,
`invProb_guessInverter` (`HardcoreBit/*`); this file adds the bit-string re-encodings the
text's conventions require (`owpPredictorSnoc`) and
the typed-family bridges (`FunFamily.predProb_glPad`, `FunFamily.invProb_glInverter`). The
*asymptotic* layer states the theorems over `Complexity.NUPPT` and `FunFamily`/`PRG`/
`Collection`; every asymptotic theorem is (i) the concrete reduction at each `n`, (ii) a
machine built by the closure calculus of `TCSlib/Complexity/Randomized/`, (iii)
negligible-function arithmetic.

**Deviation:** [PS10, Theorem 87.3] says `⟨x, r⟩` is hard-core "for `f`"; it is hard-core for
`g(x, r) = (f(x), r)` (source error 26 of the plan), which is what is stated.

**Deviation:** [PS10, Definition 78.3] mixes `k` and `n` (`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`,
`∀ k`); the formal statement takes `k = n` (source error 30), on the typed domains of D5, with
the predictor's verdict the string `[true]`.

**Deviation:** [PS10, Theorem 79.4] is proved by the direct reduction of [Gar26, Theorem 3.2]
(one call of the distinguisher on `f(s) ‖ σ` for a random bit `σ`, exact bound `1/2 + ε`)
rather than through the next-bit test (Theorem 75.4), which would lose a factor `1/ℓ`.

**Deviation:** [PS10, Lemma 80.5]: the generator `G'` outputs the bits only (the final seed is
dropped, as in the text); `G(X_i)` is read seed-first/bit-last as in the text (the concrete
`prgExt` reads bit-first; `oneBitStep` is the fixed re-encoding); the expansion clause
`ℓ(n) > n` at every `n` is an explicit hypothesis, see `PRG` (the text's "for any polynomial
`ℓ`": stretches with `ℓ(0) = 0` or `ℓ(1) = 1` are excluded; gate 03c, finding 1, ruling G3-2).
[PS10, Corollary 81.7] lists `ℓ(n) + 1` bits `i = 0, …, ℓ(n)` (source error 38) and needs
`n ≤ ℓ(n)`.

The collection form of [PS10, Theorem 87.3] and its Deviation (the encoding-length hypothesis
`henc` of `Collection.glPad`) are in `Asymptotic/HardCoreCollection.lean` (moved out of this
file for size; gate 03c, finding 11).

**Remarks (not formalized; [PS10, §3.3.2], inventory Constr-77.a, Claim-78.a, Claim-78.b).**
Shamir's generator `G(s) = f^n(s) ‖ ⋯ ‖ f(s) ‖ s` (Constr-77.a) motivates the construction
and is not formalized. Claim-78.a (for a permutation `f` and a uniform `x`, `f^k(x)` is
uniform) is an instance of `uprob_comp_equiv` (the uniform distribution is invariant under a
bijection) applied to the `k`-th iterate of the permutation; it is not stated separately.
Claim-78.b (unpredictable blocks need not have unpredictable bits: a one-way permutation may
leave input bits unchanged) has the concrete witness of [Gar26, Claim 2.3] in
`HardcoreBit/NoFixedBit.lean`: `g(x, y) = f(x_{-y}) ‖ x_y ‖ y` reveals the bits of `y` with
certainty (`predProb_positionBit`) and each fixed input bit `x_i` with advantage
`1/(2(n + 1))` (`predProb_fixedBitPredictor`).

## Main definitions

* `TCSlib.Cryptography.HardCore` — hard-core predicate for a function family
  [PS10, Definition 78.3] (frozen signature).
* `TCSlib.Cryptography.owpGenPRG` — the one-bit-stretch
  generator `f(s) ‖ h(s)` [PS10, Theorem 79.4]; `TCSlib.Cryptography.owpPredictorSnoc` — its
  predictor.
* `TCSlib.Cryptography.PermFamily.iterPRG` — `h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))`
  [PS10, Corollary 81.7].
* `TCSlib.Cryptography.FunFamily.glPad`, `FunFamily.glBit`, `FunFamily.glInverter` — the
  Goldreich–Levin setting `g(x, r) = (f(x), r)`, `h(x, r) = ⟨x, r⟩` [PS10, Theorem 87.3].
* `TCSlib.Cryptography.Collection.glPad`, `Collection.glBit`, `PermCollection.glPad`,
  `TrapdoorCollection.glPad` — the collection form (in `Asymptotic/HardCoreCollection.lean`).

## Main results

* `TCSlib.Cryptography.owp_hardcore_prg` [PS10, Theorem 79.4];
  `TCSlib.Cryptography.exists_owpPredictorSnoc` (concrete, proved).
* `TCSlib.Cryptography.cor_81_7` [PS10, Corollary 81.7] combines Theorem 79.4 with
  `prg_expand` from `Pseudorandom.Generators.Asymptotic.Stretch` through the closed form
  `PermFamily.iterPRG_eq_expand`.
* `TCSlib.Cryptography.goldreich_levin`, `FunFamily.StrongOneWay.glPad`,
  `FunFamily.StrongOneWay.glPad_hardCore` [PS10, Theorem 87.3]; the concrete claims
  `thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`, `fact_88_4`, `thm_87_3_6`, `thm_87_3_7`,
  `thm_87_3_8`, `thm_87_3_9` (proved, instances of `HardcoreBit/*`; they live in the
  sibling file `Asymptotic/HardCoreClaims.lean`, and the machine infrastructure of the fills
  in `Asymptotic/HardCoreLemmas.lean`). The "(OWP)" clause in
  `PermFamily` form (the shape consumed by Theorems 79.4, 81.7, 126.4; `glPad` has input
  length `var + var` and is never a `PermFamily`) is `OneWayPermutation.glHalf` in
  `Asymptotic/HardCorePermutation.lean` (run-3 audit P4-1).
* `TCSlib.Cryptography.goldreich_levin_coll`, `Collection.OneWay.glPad`,
  `Collection.OneWay.glPad_hardCore`, `PermCollection.OneWay.glPad`,
  `TrapdoorCollection.OneWay.glPad` [PS10, Theorem 87.3, collection form] (in
  `Asymptotic/HardCoreCollection.lean`).
* `TCSlib.Cryptography.not_hardCore_const` — a constant predicate is never hard-core
  (non-vacuity of the hardness clause of Definition 78.3).
* `TCSlib.Cryptography.hardCore_iff` and `owpPredictorSnoc_eq` give the defining equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.3: Definition 78.3; §3.3.4: Theorem 79.4; §3.3.5: Lemma 80.5, Corollary 81.7;
  §3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithms 88.5, 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figures 2.3–2.5), §3.3 (Theorems 3.1, 3.2).
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

/-! ## The generator `f(s) ‖ h(s)` [PS10, Theorem 79.4] -/

/-- The generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4] for a permutation family `f`
and a predicate `h`: output length `n + 1`, the bit `h(s)` in the last position. -/
def owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : PRG :=
  { stretch := .add .var (.const 1)
    G := fun n s => Fin.snoc (P.f n s) (h n s)
    expands := fun n => Nat.lt_succ_self n }

/-- **The outputs of the generator of Theorem 79.4 are `{0,1}^{n+1}`**: the published
equivalence `{0,1}^{stretch(n)} ≃ {0,1}^{n+1}` (the identity on the definition). -/
def owpGenPRG_outEquiv (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) :
    (Fin ((owpGenPRG P h).stretch.eval n) → Bool) ≃ (Fin (n + 1) → Bool) :=
  Equiv.refl _

/-- The generator of Theorem 79.4 through its output equivalence: `G(s) = f(s) ‖ h(s)`. -/
theorem owpGenPRG_G_outEquiv (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) :
    owpGenPRG_outEquiv P h n ((owpGenPRG P h).G n s) = Fin.snoc (P.f n s) (h n s) := rfl

/-- The output equivalence keeps the string:
`List.ofFn (owpGenPRG_outEquiv P h n y) = List.ofFn y`. -/
theorem owpGenPRG_outEquiv_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (y : Fin ((owpGenPRG P h).stretch.eval n) → Bool) :
    List.ofFn (owpGenPRG_outEquiv P h n y) = List.ofFn y := rfl

/-- Unfolding: the generator of Theorem 79.4 outputs `f(s)` on the first `n` positions. -/
theorem owpGenPRG_G_castSucc (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) (i : Fin n) : (owpGenPRG P h).G n s i.castSucc = P.f n s i := by
  simp [owpGenPRG]

/-- Unfolding: the generator of Theorem 79.4 outputs `h(s)` in the last position. -/
theorem owpGenPRG_G_last (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) : (owpGenPRG P h).G n s (Fin.last n) = h n s := by
  simp [owpGenPRG]

/-- The predictor of [Gar26, proof of Theorem 3.2] for a distinguisher of `f(s) ‖ h(s)`: on
input `y = f(s)` it draws a bit `σ` and coins for `D`, outputs `σ` if `D(y ‖ σ) = 1` and
`¬σ` otherwise, negated when `flip`. One call to `D`, one extra coin. -/
def owpPredictorSnoc {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool) (flip : Bool) :
    (Fin n → Bool) → Bool × ρ → Bool :=
  fun y c => owpPredictor (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r)
    flip (y, ()) c

/-- Unfolding: `owpPredictorSnoc D flip` is the concrete `owpPredictor` [Gar26, proof of
Theorem 3.2] for the distinguisher `(y, (), σ) ↦ D(y ‖ σ)`, at the point `(y, ())`. -/
theorem owpPredictorSnoc_eq {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool)
    (flip : Bool) (y : Fin n → Bool) (c : Bool × ρ) :
    owpPredictorSnoc D flip y c = owpPredictor
      (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r) flip (y, ()) c :=
  rfl

/-- **PRG from a one-way permutation, concrete form** [PS10, Theorem 79.4; Gar26, Theorem 3.2]:
if `D` distinguishes `f(s) ‖ B(s)` from a uniform `(n+1)`-bit string with advantage `ε`, then
for one sign `flip` the predictor `owpPredictorSnoc D flip` predicts `B(s)` from `f(s)` with
probability exactly `1/2 + ε`. Only bijectivity of `f` is used.

**Proof sketch.** Instance of `exists_owpPredictor` with the trivial second component
`β := Unit` and the bit `B'(s, ()) = B(s)`: `owpPair f ≃ f` and `owpGen f B' ≃ f(s) ‖ B(s)`
under the bijections `(s, ()) ↦ s` (seeds, `acceptProb_fst`) and
`(y, (), b) ↦ y ‖ b` (outputs, `prgAdv_comp_equiv`); the prediction experiments correspond
under `(s, c) ↦ ((s, ()), c)` (`uprob_eq_of_equiv`). -/
theorem exists_owpPredictorSnoc {ρ : Type*} [Fintype ρ] [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (B : (Fin n → Bool) → Bool)
    (D : (Fin (n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb f B (owpPredictorSnoc D flip) =
      1 / 2 + prgAdv (fun s => Fin.snoc (f s) (B s)) D := by
  let e : (Fin n → Bool) × Unit × Bool ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun z => Fin.snoc z.1 z.2.2
      invFun := fun t => (Fin.init t, (), t (Fin.last n))
      left_inv := fun z => by
        obtain ⟨a, -, b⟩ := z
        simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun t => by simp [Fin.snoc_init_self] }
  obtain ⟨flip, hflip⟩ := exists_owpPredictor (β := Unit) f (fun w => B w.1)
    (fun z r => D (e z) r)
  refine ⟨flip, ?_⟩
  have h1 : predProb f B (owpPredictorSnoc D flip) =
      predProb (owpPair f) (fun w : (Fin n → Bool) × Unit => B w.1)
        (owpPredictor (fun z r => D (e z) r) flip) := by
    simp only [predProb_def]
    exact uprob_eq_of_equiv
      ({ toFun := fun z : (Fin n → Bool) × (Bool × ρ) => ((z.1, ()), z.2)
         invFun := fun z => (z.1.1, z.2)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (Fin n → Bool) × (Bool × ρ) ≃ ((Fin n → Bool) × Unit) × (Bool × ρ))
      fun _ => Iff.rfl
  have h2 : prgAdv (fun s => Fin.snoc (f s) (B s)) D =
      prgAdv (owpGen f fun w : (Fin n → Bool) × Unit => B w.1) (fun z r => D (e z) r) := by
    rw [← prgAdv_comp_equiv e]
    simp only [prgAdv_eq, distAdv_def]
    rw [← acceptProb_fst (τ := Unit) (fun s => Fin.snoc (f s) (B s)) D]
    rfl
  rw [h1, h2, hflip]

/-- **PRG from a one-way permutation** [PS10, Theorem 79.4]: if `f` is a one-way permutation
and `h` is a hard-core predicate for `f`, then `G(s) = f(s) ‖ h(s)` is a pseudorandom
generator.

**Deviation:** proved by the direct reduction of [Gar26, Theorem 3.2] (one call of `D` on
`f(s) ‖ σ` for a random bit `σ`, exact bound `1/2 + ε`) rather than through the next-bit
test as in the text (which loses a factor `1/(n+1)`); the text's proof writes "predicts
the `i`th bit with probability `1/p(n)`" for "advantage" and "`b` is hard-core" for `h`.

**Proof sketch.** *Easy:* from `hP.easy = ⟨F, hF, hFx⟩` and `hh.easy = ⟨H, hH, hHx⟩` the
evaluator `s ↦ F ⟨1^{|s|}, s⟩ ++ H ⟨1^{|s|}, s⟩` is polynomial-time
(`polyTimeComputable_unary`, `PolyTimeComputable.pairEncode`, `.comp`, `.append`) and
computes `List.ofFn (Fin.snoc (f s) (h s)) = List.ofFn (f s) ++ [h s]` (`List.ofFn_succ'`,
`Fin.snoc_castSucc`, `Fin.snoc_last`). *Pseudorandom:* fix `D : NUPPT`. At every `n`,
`exists_owpPredictorSnoc (P.f n) (h n) (D.distinguisher n (n+1))` gives a sign `flip_n`
(chosen by `Classical.choose`). The predictor machine `A`: advice `⟨[flip_n], D.advice n⟩`
(`NUPPT.exists_withAdvice`, length `≤ D.adv + 6`), coins `1 + D.coins`
(`NUPPT.exists_split (const 1)`: the first coin `σ` is passed as data), on `⟨1^n, y⟩` it forms
`y ++ [σ]` (`PolyTimeComputable.append`), calls `D` once on `⟨1^n, y ++ [σ]⟩` with the remaining
coins (`NUPPT.exists_seq`) and outputs `[xor (if D accepts then σ else !σ) flip_n]`
(`polyTimeComputable_ite`, `polyTimeComputable_pairEq`, `NUPPT.exists_comp`). Functional
identity: `A.predictor n n y r = owpPredictorSnoc (D.distinguisher n (n+1)) flip_n y (c r)`
with `c : A.Coins n ≃ Bool × D.Coins n` the coin split (`Fin.consEquiv`), so
`predProb (P.f n) (h n) (A.predictor n n) = 1/2 + prgAdv ((owpGenPRG P h).G n) (D.distinguisher n (n+1))`
(`uprob_comp_equiv`). Then `hh.hard A` gives a negligible `ε` with the left side `≤ 1/2 + ε n`,
so `0 ≤ prgAdv ≤ ε n` for all `n` and `Negligible.mono` closes `PRG.secure_iff`. -/
theorem owp_hardcore_prg (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hP : OneWayPermutation P) (hh : P.HardCore h) : (owpGenPRG P h).Secure := by
  obtain ⟨F, hF, hFx⟩ := hP.evaluator
  obtain ⟨H, hH, hHx⟩ := hh.easy
  rw [PRG.secure_iff]
  refine ⟨(PRG.easy_iff _).2 (exists_owpGenEvaluator P h hF hH hFx hHx), fun D => ?_⟩
  have hflip : ∀ n, ∃ flip : Bool,
      predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) flip) =
        1 / 2 + prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) :=
    fun n => exists_owpPredictorSnoc (P.f n) (h n) _
  choose flip hflip using hflip
  obtain ⟨ε, hε, hbound⟩ := hh.hard (owpPredMachine D flip)
  refine hε.mono ⟨0, fun n _ => ?_⟩
  have h1 : predProb (P.f n) (h n) ((owpPredMachine D flip).predictor n n) ≤ 1 / 2 + ε n :=
    hbound n
  rw [owpPredMachine_predProb] at h1
  have h2 := hflip n
  have h3 : predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) (flip n)) =
      predProb (P.f n) (h n) (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) :=
    congrArg _ (funext fun y => funext fun c => by rw [owpPredictorSnoc_eq, owpPredictor_apply])
  rw [← h3, h2] at h1
  show |prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1))| ≤ |ε n|
  have h4 : 0 ≤ prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) := by
    rw [prgAdv_eq, distAdv_def]
    exact abs_nonneg _
  rw [abs_of_nonneg h4]
  exact le_trans (by linarith) (le_abs_self _)

/-! ## The iterated generator [PS10, Corollary 81.7] -/

/-- The generator `G(x) = h(x) ‖ h(f(x)) ‖ h(f^{(2)}(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` of
[PS10, Corollary 81.7]: output bit `i` (`0 ≤ i ≤ ℓ(n)`) is `h(f^{(i)}(x))`; output length
`ℓ(n) + 1`, expanding when `n ≤ ℓ(n)`.

**Deviation:** the text's formula lists `ℓ(n) + 1` bits where Lemma 80.5 produces `ℓ(n)`
(source error 38); the stretch is `ℓ + 1` and the expansion hypothesis is `n ≤ ℓ(n)`. -/
def PermFamily.iterPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) : PRG where
  stretch := .add ℓ (.const 1)
  G n s := fun i => h n ((⇑(P.f n))^[i] s)
  expands n := Nat.lt_succ_of_le (hℓ n)

/-- **The closed form of Corollary 81.7**: the iterated generator is the `(ℓ(n) + 1)`-bit
expansion (Lemma 80.5) of the one-bit generator `f(s) ‖ h(s)` (Theorem 79.4), since the seed
update of `oneBitStep (f(s) ‖ h(s))` is `f` (`Fin.init_snoc`) and its output bit is `h`
(`Fin.snoc_last`).

**Proof sketch.** Read the expanded generator’s stretch and output from its field equations.
The seed update and emitted bit simplify to `f` and `h`. Rewrite the stretch first to
align the dependent output types, then compare the generators pointwise. -/
theorem PermFamily.iterPRG_eq_expand (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (ℓ : PolyExpr) (hℓ : ∀ n, n ≤ ℓ.eval n) :
    P.iterPRG h ℓ hℓ = PRG.expand (fun n s => Fin.snoc (P.f n s) (h n s)) (.add ℓ (.const 1))
      (fun n => Nat.lt_succ_of_le (hℓ n)) := by
  let G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
    fun n s => Fin.snoc (P.f n s) (h n s)
  let Q := PRG.expand G (.add ℓ (.const 1)) (fun n => Nat.lt_succ_of_le (hℓ n))
  have hlen : Q.stretch = .add ℓ (.const 1) := PRG.expand_stretch _ _ _
  have hclosed (n : ℕ) (s : Fin n → Bool) (i : Fin (Q.stretch.eval n)) :
      Q.G n s i = h n ((⇑(P.f n))^[i] s) := by
    change (PRG.expand G _ _).G n s i = _
    rw [PRG.expand_G_stretch]
    simp only [G, Fin.init_snoc, Fin.snoc_last]
  change P.iterPRG h ℓ hℓ = Q
  generalize Q = R at hlen hclosed ⊢
  cases R with
  | mk len out expands =>
    change len = .add ℓ (.const 1) at hlen
    subst len
    unfold PermFamily.iterPRG
    congr 1
    funext n s i
    exact (hclosed n s i).symm

/-- **The iterated generator is a PRG** [PS10, Corollary 81.7]: for a one-way permutation `f`
with hard-core predicate `h`, `G(x) = h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` is a PRG, by
Theorem 79.4 (`owp_hardcore_prg`) and Lemma 80.5 (`prg_expand`) through the closed form
`PermFamily.iterPRG_eq_expand`. -/
theorem cor_81_7 (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) (hP : OneWayPermutation P) (hh : P.HardCore h) :
    (P.iterPRG h ℓ hℓ).Secure := by
  rw [PermFamily.iterPRG_eq_expand]
  apply prg_expand
  have hgen := owp_hardcore_prg P h hP hh
  rw [PRG.secure_iff, PRG.easy_iff] at hgen
  exact (PRG.oneBit_secure_iff _).2 hgen

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
`OneWayPermutation.glHalf` (`Asymptotic/HardCorePermutation.lean`, `glHalf_f_even`). -/
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
`PermFamily`. That route is `OneWayPermutation.glHalf` (`Asymptotic/HardCorePermutation.lean`):
the balanced permutation `PermFamily.glHalf`, `x ‖ w ↦ f_{⌊n/2⌋}(x) ‖ w`, whose one-wayness and
hard-core bit reduce to `StrongOneWay.glPad` and `StrongOneWay.glPad_hardCore` at parameter
`⌊n/2⌋` through `predProb_glHalf_even`/`predProb_glHalf_odd`, `invProb_glHalf_even`/
`invProb_glHalf_odd_le` and `Negligible.comp_div_two`. -/
theorem goldreich_levin {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    𝓕.glPad.StrongOneWay ∧ HardCore 𝓕.glPad 𝓕.glBit :=
  ⟨h.glPad, h.glPad_hardCore⟩

end TCSlib.Cryptography
