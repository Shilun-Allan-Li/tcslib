/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.NextBit
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.Asymptotic.HardCoreGL
import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
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
# Hard-core predicates, generators from one-way permutations, Goldreich–Levin

The material of [PS10, §3.3.3–§3.3.5 and §3.4.2–§3.4.3]: hard-core predicates
[PS10, Definition 78.3]; the one-bit-stretch generator `G(s) = f(s) ‖ h(s)` from a one-way
permutation `f` with hard-core predicate `h` [PS10, Theorem 79.4]; the expansion of a
one-bit-stretch generator to `ℓ(n)` bits [PS10, Lemma 80.5]; the iterated generator
`h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` [PS10, Corollary 81.7]; and the Goldreich–Levin theorem:
for every one-way function `f`, `g(x, r) = (f(x), r)` is one-way and `⟨x, r⟩` is hard-core for
`g` [PS10, Theorem 87.3], together with the concrete claims of its proof (the oversimplified
case, the `3/4 + ε` case, the good set, Fact 88.4, Algorithms 88.5 and 89.6, the
pairwise-independence and union-bound claims, the final bound) and the version for
collections of (trapdoor) permutations needed by [PS10, Theorem 104.4].

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer is
the frozen Garg development reused verbatim: `owpPredictor`/`exists_owpPredictor`
(`Pseudorandom/GeneratorFromPermutation.lean`), `prgExt`/`prgExtRed`/`exists_prgExtRed_ge`
(`Pseudorandom/Generators.lean`), `HardcoreBit.glPad`, `glBit`, `guessInverter`,
`invProb_guessInverter` (`HardcoreBit/*`); this file adds the bit-string re-encodings the
text's conventions require (`owpPredictorSnoc`, `oneBitStep`, `expandRed`, `prgAdv_fst`) and
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
`ℓ(n) > n` is an explicit hypothesis. [PS10, Corollary 81.7] lists `ℓ(n) + 1` bits
`i = 0, …, ℓ(n)` (source error 38) and needs `n ≤ ℓ(n)`.

**Deviation:** [PS10, Theorem 87.3] for collections (unnumbered): the padded collection
`Collection.glPad F m` pads each element by `|encD_i(default)|` uniform bits; its one-wayness
and hard-core theorems assume length-regular encodings at generated indices
(`∀ n r x, |encD_{index n r} x| = m(n)`), which the text's "`|x| = |r|`" presupposes. Its
hard-core proof uses the encoded-domain Goldreich–Levin lemma
`HardcoreBit.invProb_guessInverter_enc_pad` (`Asymptotic/GoldreichLevinDomain.lean`): the
cube lemma does not transfer to a domain `D_i` whose encoding is a strict subset of the cube
(run-3 audit P4-2).

## Main definitions

* `TCSlib.Cryptography.HardCore` — hard-core predicate for a function family
  [PS10, Definition 78.3] (frozen signature).
* `TCSlib.Cryptography.PRG.oneBit`, `TCSlib.Cryptography.owpGenPRG` — the one-bit-stretch
  generator `f(s) ‖ h(s)` [PS10, Theorem 79.4]; `TCSlib.Cryptography.owpPredictorSnoc` — its
  predictor.
* `TCSlib.Cryptography.oneBitStep`, `TCSlib.Cryptography.PRG.expand`,
  `TCSlib.Cryptography.expandRed` — the expansion `G'` of [PS10, Lemma 80.5] and its reduction.
* `TCSlib.Cryptography.PermFamily.iterPRG` — `h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))`
  [PS10, Corollary 81.7].
* `TCSlib.Cryptography.FunFamily.glPad`, `FunFamily.glBit`, `FunFamily.glInverter` — the
  Goldreich–Levin setting `g(x, r) = (f(x), r)`, `h(x, r) = ⟨x, r⟩` [PS10, Theorem 87.3].
* `TCSlib.Cryptography.Collection.glPad`, `Collection.glBit`, `PermCollection.glPad`,
  `TrapdoorCollection.glPad` — the collection form.

## Main results

* `TCSlib.Cryptography.owp_hardcore_prg` [PS10, Theorem 79.4];
  `TCSlib.Cryptography.exists_owpPredictorSnoc` (concrete, proved).
* `TCSlib.Cryptography.prg_expand` [PS10, Lemma 80.5]; `TCSlib.Cryptography.exists_expandRed_ge`
  (concrete, proved).
* `TCSlib.Cryptography.cor_81_7` [PS10, Corollary 81.7] (proved from the two above and the
  closed form `PermFamily.iterPRG_eq_expand`).
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
  `TrapdoorCollection.OneWay.glPad` [PS10, Theorem 87.3, collection form].
* `TCSlib.Cryptography.not_hardCore_const` — a constant predicate is never hard-core
  (non-vacuity of the hardness clause of Definition 78.3).

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

/-- The efficiency clause of a hard-core predicate [PS10, Definition 78.3 (1)]. -/
theorem HardCore.easy {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
    (hh : HardCore 𝓕 h) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x] := hh.1

/-- The unpredictability clause of a hard-core predicate [PS10, Definition 78.3 (2)]. -/
theorem HardCore.hard {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
    (hh : HardCore 𝓕 h) (A : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n := hh.2 A

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
    simp only [NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt, NUPPT.ofPolyTimeUniform,
      NUPPT.output_ofPolyTime]
    cases b <;> simp
  obtain ⟨n₀, hn₀⟩ := hε 1
  have h1 := h (max n₀ 2)
  rw [hone] at h1
  have h2 := hn₀ (max n₀ 2) (le_max_left _ _)
  have h3 : (2 : ℝ) ≤ max n₀ 2 := by exact_mod_cast le_max_right n₀ 2
  have h4 : 1 / ((max n₀ 2 : ℕ) : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]
    exact one_div_le_one_div_of_le (by norm_num) h3
  linarith [le_abs_self (ε (max n₀ 2))]

/-! ## The generator `f(s) ‖ h(s)` [PS10, Theorem 79.4] -/

/-- A one-bit-stretch generator `G n : {0,1}^n → {0,1}^{n+1}` as a `PRG` with stretch
`n + 1` ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG", [PS10, Lemma 80.5]). -/
def PRG.oneBit (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) : PRG where
  stretch := .add .var (.const 1)
  G := G
  expands n := Nat.lt_succ_self n

/-- The generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4] for a permutation family `f`
and a predicate `h`: output length `n + 1`, the bit `h(s)` in the last position. -/
def owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : PRG :=
  PRG.oneBit fun n s => Fin.snoc (P.f n s) (h n s)

/-- Unfolding: the generator of Theorem 79.4 outputs `f(s)` on the first `n` positions. -/
theorem owpGenPRG_G_castSucc (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) (i : Fin n) : (owpGenPRG P h).G n s i.castSucc = P.f n s i := by
  simp [owpGenPRG, PRG.oneBit]

/-- Unfolding: the generator of Theorem 79.4 outputs `h(s)` in the last position. -/
theorem owpGenPRG_G_last (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) : (owpGenPRG P h).G n s (Fin.last n) = h n s := by
  simp [owpGenPRG, PRG.oneBit]

/-- The predictor of [Gar26, proof of Theorem 3.2] for a distinguisher of `f(s) ‖ h(s)`: on
input `y = f(s)` it draws a bit `σ` and coins for `D`, outputs `σ` if `D(y ‖ σ) = 1` and
`¬σ` otherwise, negated when `flip`. One call to `D`, one extra coin. -/
def owpPredictorSnoc {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool) (flip : Bool) :
    (Fin n → Bool) → Bool × ρ → Bool :=
  fun y c => owpPredictor (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r)
    flip (y, ()) c

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
    unfold predProb
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
    unfold prgAdv distAdv
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
    (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) : (owpGenPRG P h).Secure := by
  obtain ⟨F, hF, hFx⟩ := hP.easy
  obtain ⟨H, hH, hHx⟩ := hh.easy
  refine ⟨exists_owpGenEvaluator P h hF hH hFx hHx, fun D => ?_⟩
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
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := rfl
  rw [← h3, h2] at h1
  show |prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1))| ≤ |ε n|
  have h4 : 0 ≤ prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) :=
    abs_nonneg _
  rw [abs_of_nonneg h4]
  exact le_trans (by linarith) (le_abs_self _)

/-! ## Expansion of a one-bit-stretch generator [PS10, Lemma 80.5] -/

/-- A one-bit-stretch generator read in the text's order `X_{i+1} ‖ b_{i+1} ← G(X_i)`
[PS10, Lemma 80.5]: the output bit is the last bit of `G(s)` and the next seed is its first
`n` bits (`(Fin.snocEquiv _).symm (G s)`); this is the `S → Bool × S` form of
[Gar26, Construction 3.1], which reads the bit first. -/
def oneBitStep {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (Fin n → Bool) → Bool × (Fin n → Bool) :=
  fun s => (G s (Fin.last n), Fin.init (G s))

/-- The **expanded generator** `G'(s) = b_1 ⋯ b_{ℓ(n)}` of [PS10, Lemma 80.5]: `X_0 = s`,
`X_{i+1} ‖ b_{i+1} ← G(X_i)`, output the `ℓ(n)` bits (the final seed is dropped). Formally
the first component of the concrete `prgExt (oneBitStep (G n)) (ℓ n)` [Gar26,
Construction 3.1]; the expansion clause `n < ℓ(n)` is the hypothesis `hℓ`.

**Deviation:** `G(X_i)` is read seed-first/bit-last as in the text; the output drops the
final seed (as in the text), the concrete `prgExt` keeps it. -/
def PRG.expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) : PRG where
  stretch := ℓ
  G n s := (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1
  expands := hℓ

/-- Closed form of the expansion: output bit `i` is the last bit of `G(X_i)`, where
`X_i` is the `i`-th iterate of `s ↦ init (G s)` on the seed (`b_{i+1}` in the text's
1-indexed notation). -/
theorem PRG.expand_G (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (n : ℕ) (s : Fin n → Bool) (i : Fin (ℓ.eval n)) :
    (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := rfl

/-- The hybrid-`k` reduction of [PS10, Lemma 80.5] (the machine `M(y)` of the proof) in the
text's seed-first convention: on `T ∈ {0,1}^{n+1}` read `(b, X) := (T_{n+1}, T_1 ⋯ T_n)`, draw
`k` uniform bits `b_prev`, put `b` at position `k`, iterate `G` on `X` for the remaining
positions and call `D` once on the `ℓ` bits. Cost: that of `prgExtRed` (`l − k − 1` calls to
`G`, one to `D`, `l` coins of which `k` are used). -/
def expandRed {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (l k : ℕ)
    (D : (Fin l → Bool) → ρ → Bool) : (Fin (n + 1) → Bool) → (Fin l → Bool) × ρ → Bool :=
  fun T c => prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c

/-- Dropping an independent uniform component from a generator's output does not change
PRG advantages: `prgAdv (fst ∘ X) D = prgAdv X (D ∘ fst)` (the projection is a deterministic
post-processing and the projection of a uniform pair is uniform). -/
theorem prgAdv_fst {σ γ δ ρ : Type*} [Fintype σ] [Fintype γ] [Fintype δ] [Nonempty δ]
    [Fintype ρ] (X : σ → γ × δ) (D : γ → ρ → Bool) :
    prgAdv (fun s => (X s).1) D = prgAdv X (fun z r => D z.1 r) := by
  unfold prgAdv distAdv
  rw [← acceptProb_fst (τ := δ) (id : γ → γ) D]
  rfl

/-- **Expansion, concrete form** [PS10, Lemma 80.5; Gar26, Theorem 3.1]: if `D` distinguishes
the `l`-bit expansion of `G` (`l ≥ 1`, bits only) from a uniform `l`-bit string with advantage
`ε`, then for some hybrid index `k < l` the reduction `expandRed G l k D` distinguishes
`G` from a uniform `(n+1)`-bit string with advantage at least `ε / l`.

**Proof sketch.** `prgAdv_fst` moves the projection onto the distinguisher;
`exists_prgExtRed_ge` for `oneBitStep G` gives `k`; `prgAdv_comp_equiv` with the bijection
`(Fin.snocEquiv _).symm : {0,1}^{n+1} ≃ Bool × {0,1}^n` re-encodes the reduction's input. -/
theorem exists_expandRed_ge {ρ : Type*} [Fintype ρ] {n : ℕ}
    (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) {l : ℕ} (hl : 0 < l)
    (D : (Fin l → Bool) → ρ → Bool) :
    ∃ k < l, prgAdv (fun s => (prgExt (oneBitStep G) l s).1) D / l ≤
      prgAdv G (expandRed G l k D) := by
  obtain ⟨k, hk, h⟩ := exists_prgExtRed_ge (oneBitStep G) hl (fun z r => D z.1 r)
  refine ⟨k, hk, ?_⟩
  rw [prgAdv_fst]
  refine h.trans_eq ?_
  exact prgAdv_comp_equiv (Fin.snocEquiv fun _ => Bool).symm G
    (prgExtRed (oneBitStep G) l k fun z r => D z.1 r)

/-- **Expansion of a PRG** [PS10, Lemma 80.5]: if the one-bit-stretch generator `G` is a PRG
then so is its `ℓ(n)`-bit expansion `G'` (`ℓ(n) > n`).

**Deviation:** `G'` drops the final seed and reads `G(X_i)` seed-first, as the text; the
text's proof interchanges `m(n)` and `ℓ(n)`, starts the hybrids at `i = 1` (they must start
at `0`) and reads `M(y)` bit-first against the construction (source error 34).

**Proof sketch.** *Easy:* from `h.1 = ⟨F, hF, hFs⟩`, `G'` is computed by
`polyTimeComputable_iterateEmit` with step `x ↦ (F x).dropLast` (the next seed,
`Turing.FinTM.computesFunInTime_stripLast`) and emission `x ↦ [(F x).getLast]`, `R := ℓ`,
orbit bound `P := var` (all seeds have length `n`), truncated to the first `ℓ(n)` bits
(`polyTimeComputable_pairTakePoly ℓ` on `⟨1^{|s|}, ·⟩`); the identity with
`PRG.expand_G` is `List.ofFn_succ'`. *Pseudorandom* (`PRG.secure_iff`): fix `D : NUPPT`.
At every `n`, `exists_expandRed_ge (G n) (hl := Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n))`
with `D.distinguisher n (ℓ n)` gives a hybrid index `k_n < ℓ(n)`. The reduction machine
`M`: advice `⟨⟨1^{k_n}, 1^{ℓ(n) − k_n − 1}⟩, D.advice n⟩` (`NUPPT.exists_withAdvice`,
length `≤ 2ℓ + D.adv + 8`), coins `ℓ + D.coins` (`NUPPT.exists_split ℓ`), on `⟨1^n, T⟩` it
takes the first `k_n` coins as `b_prev` (`pairTakePoly`), the last bit of `T` as `b` and its
first `n` bits as `X` (`stripLast`, `pairDropPoly`), iterates `F` `ℓ(n) − k_n − 1` times
emitting the last bits (`polyTimeComputable_iterateEmit` with the unary advice as fuel),
concatenates `b_prev ++ [b] ++ b_next` and calls `D` once (`NUPPT.exists_seq`). Functional
identity: `M.distinguisher n (n+1) T r = expandRed (G n) (ℓ n) k_n (D.distinguisher n (ℓ n)) T (c r)`
with `c : M.Coins n ≃ (Fin (ℓ n) → Bool) × D.Coins n` (`Fin.appendEquiv`), hence
`prgAdv (G n) (M.distinguisher n (n+1)) ≥ prgAdv ((PRG.expand G ℓ hℓ).G n) (D.distinguisher n (ℓ n)) / ℓ(n)`
(`uprob_comp_equiv`). By `h.2 M` the left side is negligible; `ℓ(n) ≤ C (n+1)^c`
(`PolyExpr.eval_le`), so the right side is negligible by `Negligible.mul_pow`,
`Negligible.const_mul` and `Negligible.mono`. -/
theorem prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure := by
  rw [PRG.secure_iff] at h ⊢
  obtain ⟨⟨F, hF, hFs⟩, hsec⟩ := h
  have hFs' : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s) := hFs
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := exists_expandEvaluator G hFs' hF ℓ
    exact ⟨E, hE, fun n s => by rw [hEs]; rfl⟩
  · have hk : ∀ n, ∃ k < ℓ.eval n,
        prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1) (D.distinguisher n (ℓ.eval n)) /
          ℓ.eval n ≤
        prgAdv (G n) (expandRed (G n) (ℓ.eval n) k (D.distinguisher n (ℓ.eval n))) :=
      fun n => exists_expandRed_ge (G n) (Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)) _
    choose k hk hle using hk
    have hneg : Negligible fun n =>
        prgAdv (G n) ((expandRedMachine D hF ℓ k hk).distinguisher n (n + 1)) :=
      hsec (expandRedMachine D hF ℓ k hk)
    have hred : ∀ n, prgAdv (G n) ((expandRedMachine D hF ℓ k hk).distinguisher n (n + 1)) =
        prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n))) := by
      intro n
      refine prgAdv_coins_equiv _ _ _ (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)) fun T c => ?_
      obtain ⟨a, c⟩ := c
      exact expandRedMachine_distinguisher G hFs' D hF ℓ k hk n T a c _ (ofFn_appendEquiv a c)
    simp only [hred] at hneg
    refine (hneg.polyExpr_mul ℓ).mono ⟨0, fun n _ => ?_⟩
    have hpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)
    have h1 := hle n
    rw [div_le_iff₀ hpos] at h1
    show |prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1) (D.distinguisher n (ℓ.eval n))| ≤
      |(ℓ.eval n : ℝ) * prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n)))|
    have h2 : 0 ≤ prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1)
        (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    have h3 : 0 ≤ prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n))) :=
      abs_nonneg _
    rw [abs_of_nonneg h2, abs_of_nonneg (mul_nonneg hpos.le h3)]
    linarith

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
(`Fin.snoc_last`). -/
theorem PermFamily.iterPRG_eq_expand (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (ℓ : PolyExpr) (hℓ : ∀ n, n ≤ ℓ.eval n) :
    P.iterPRG h ℓ hℓ = PRG.expand (fun n s => Fin.snoc (P.f n s) (h n s)) (.add ℓ (.const 1))
      (fun n => Nat.lt_succ_of_le (hℓ n)) := by
  unfold PermFamily.iterPRG PRG.expand
  congr 1
  funext n s i
  have hstep : prgStep (oneBitStep fun x => Fin.snoc (P.f n x) (h n x)) = ⇑(P.f n) :=
    funext fun x => by
      show Fin.init (Fin.snoc (P.f n x) (h n x) : Fin (n + 1) → Bool) = P.f n x
      exact Fin.init_snoc _ _
  simp only [prgExt]
  rw [hstep]
  simp only [oneBitStep, Fin.snoc_last]

/-- **The iterated generator is a PRG** [PS10, Corollary 81.7]: for a one-way permutation `f`
with hard-core predicate `h`, `G(x) = h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` is a PRG, by
Theorem 79.4 (`owp_hardcore_prg`) and Lemma 80.5 (`prg_expand`) through the closed form
`PermFamily.iterPRG_eq_expand`. -/
theorem cor_81_7 (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) :
    (P.iterPRG h ℓ hℓ).Secure := by
  rw [PermFamily.iterPRG_eq_expand]
  exact prg_expand _ _ _ (owp_hardcore_prg P h hP hh)

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

/-- **Bridge to the concrete setting (prediction)**: the prediction probability of `A` for
`h = ⟨x, r⟩` of the family `g` equals that of `A ∘ (append)` for `glBit` of the concrete
`HardcoreBit.glPad (f n)` [Gar26, Theorem 2.3]. -/
theorem predProb_glPad {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) :
    predProb (𝓕.glPad.f n) (𝓕.glBit n) A =
      predProb (HardcoreBit.glPad (𝓕.f n)) HardcoreBit.glBit
        (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) := by
  unfold predProb
  exact uprob_eq_of_equiv (splitPair (𝓕.inLen.eval n) (𝓕.inLen.eval n) ρ) fun _ => Iff.rfl

/-- **Bridge to the concrete setting (inversion)**: the inversion probability of the family
inverter `glInverter n R` against the family `g` equals that of the concrete
`HardcoreBit.glInverter R` against `HardcoreBit.glPad (f n)`. -/
theorem invProb_glInverter {γ : Type*} [Fintype γ] (n : ℕ)
    (R : (Fin (𝓕.outLen.eval n) → Bool) → γ → Fin (𝓕.inLen.eval n) → Bool) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n R) =
      invProb (HardcoreBit.glPad (𝓕.f n)) (HardcoreBit.glInverter R) := by
  unfold invProb
  refine uprob_eq_of_equiv (splitPair (𝓕.inLen.eval n) (𝓕.inLen.eval n) γ) fun z => ?_
  simp only [glPad, glInverter, splitPair, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
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
  obtain ⟨F, hF, hFx⟩ := h.easy
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := exists_glPadEvaluator 𝓕 hF hFx
    refine ⟨E, hE, fun n z => ?_⟩
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
    obtain ⟨n₀, hn₀⟩ := hBneg (c + d + 1)
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

/-! ## Goldreich–Levin for collections [PS10, Theorem 87.3, collection form] -/

namespace Collection

variable (F : Collection)

/-- The **padded collection** `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] for a
collection `{f_i : D_i → R_i}` whose elements have encoding length `m(n)` at the indices
generated at parameter `n` (`henc`): the domain `D'_i = D_i × {0,1}^{|encD_i(default)|}` (the
padding has the length of the encoded elements), elements encoded as `⟨encD_i x, r⟩`, the
same index generator `Gen`, the sampler `Sample'(1^n, i) = ⟨Sample(1^n, i), r⟩` with `m(n)`
fresh coins `r`, and the evaluator `⟨i, ⟨x, r⟩⟩ ↦ ⟨eval ⟨i, x⟩, r⟩`. The sampler's outputs
decode (`sample_spec`): the first component by `F.sample_spec`, the padding because it has
exactly `m(n) = |encD_i(default)|` bits by `henc`.

Repair (run-3 audit P3-1): the hypothesis `henc` (previously carried by the theorems only) is
now an argument of the definition, since without it the padding of the sampled string need not
have the length the decoder expects and `Collection.sample_spec` would fail.

**Deviation:** the text's "`|x| = |r|`" presupposes that all elements of `D_i` have the same
encoding length; `glPad` assumes `|encD_i x| = m(n)` at generated indices (`henc`). -/
noncomputable def glPad (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    Collection where
  D i := F.D i × (Fin (F.encD i default).length → Bool)
  encD i z := pairEncode (F.encD i z.1) (List.ofFn z.2)
  decD i w := match pairDecode w with
    | some (a, b) => match F.decD i a, decodeFin (F.encD i default).length b with
      | some x, some r => some (x, r)
      | _, _ => none
    | none => none
  decD_encD i z := by simp [pairDecode_pairEncode, F.decD_encD, decodeFin_ofFn]
  f i z := pairEncode (F.f i z.1) (List.ofFn z.2)
  gen := F.gen
  gen_uniform := F.gen_uniform
  sample := NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval w := pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w))))
    (pairSndD (pairSndD w))
  eval_poly := (F.eval_poly.comp (polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  eval_spec i z := by simp [F.eval_spec]
  sample_spec n r s := by
    obtain ⟨⟨s₁, s₂⟩, hs⟩ := (Fin.appendEquiv (F.sample.coins.eval n) (m.eval n)).surjective s
    have hofn : List.ofFn s = List.ofFn s₁ ++ List.ofFn s₂ := by
      rw [← hs]
      exact List.ofFn_fin_append s₁ s₂
    have hA : (List.ofFn s).take (F.sample.coinLen n) = List.ofFn s₁ := by
      rw [hofn, List.take_left' List.length_ofFn]
    have hB : (List.ofFn s).drop (F.sample.coinLen n) = List.ofFn s₂ := by
      rw [hofn, List.drop_left' List.length_ofFn]
    obtain ⟨x, hx, hev⟩ := F.sample_spec n r s₁
    have hL : (F.encD (pairFstD (F.gen.runAt n [] r)) default).length = m.eval n := henc n r default
    have hs₂ : List.ofFn s₂ = List.ofFn
        fun j : Fin (F.encD (pairFstD (F.gen.runAt n [] r)) default).length => s₂ (Fin.cast hL j) :=
      List.ofFn_congr hL.symm s₂
    refine ⟨(x, fun j => s₂ (Fin.cast hL j)), ?_, ?_⟩
    · simp only [glPadSample_runAt, hA, hB, pairDecode_pairEncode, ← NUPPT.runAt_eq, hx, hs₂,
        decodeFin_ofFn]
    · simp only [glPadSample_runAt, hA, hB, pairFstD_pairEncode, pairSndD_pairEncode,
        ← NUPPT.runAt_eq, hev, hs₂]

/-- The predicate `h_i(x, r) = ⟨x, r⟩` for the padded collection: the inner product of the
encoding of `x` (padded or truncated to the padding length) with `r`. -/
def glBit : ∀ i, F.D i × (Fin (F.encD i default).length → Bool) → Bool :=
  fun i z => HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2

variable {F} in
/-- Unfolding: the padded collection keeps the index generator. -/
theorem glPad_gen (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    (F.glPad m henc).gen = F.gen := rfl

variable {F} in
/-- Unfolding: `g_i(x, r) = ⟨f_i(x), r⟩`. -/
theorem glPad_f (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) (z : (F.glPad m henc).D i) :
    (F.glPad m henc).f i z = pairEncode (F.f i z.1) (List.ofFn z.2) := rfl

variable {F} in
/-- Unfolding: the sampler of the padded collection runs `Sample(1^n, i)` on its first
`|Sample's coins|` coins and appends the remaining coins. -/
theorem glPad_sample_runAtL (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (n : ℕ) (i r : List Bool) :
    (F.glPad m henc).sample.runAtL n i r =
      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)) := by
  simp only [glPad, NUPPT.runAtL, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
    NUPPT.coinLen]

variable {F} in
/-- Unfolding: the decoder of the padded collection is `glPadDecode` at the padding length
`|encD_i(default)|` (propositional: the two `match` expressions are compiled separately). -/
theorem glPad_decD_eq (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) : (F.glPad m henc).decD i = glPadDecode F i (F.encD i default).length := by
  funext w
  unfold Collection.glPad glPadDecode
  dsimp only
  cases pairDecode w with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    dsimp only
    cases F.decD i a <;> cases decodeFin (F.encD i default).length b <;> rfl

/-- **The padded collection is one-way** ([PS10, Theorem 87.3], collection form, first clause):
if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at the
indices generated at parameter `n`, then `F.glPad m` is a collection of one-way functions.

**Proof sketch.** *Sampling:* with `h.sampleClose = ⟨δ, hδ, hS⟩`, at index `i = index n r`
the decoded sampler output is `(decD i (Sample(1^n, i; s₁)), decodeFin _ (ofFn s₂))` on the
coin split `splitCoins (Sample.coins n) (m n)` (`glPad_sample_runAtL`, `List.ofFn` of the
split, `uprob_comp_equiv`); `henc` gives `(encD i default).length = m n`, so the second
component decodes exactly (`decodeFin_ofFn`) and `StatClose.prod (hS n r) (StatClose.refl _)`
with `StatClose.map` to the pair gives `SampleClose δ`. *Hard:* for `A : NUPPT` against
`F.glPad m`, the inverter `B` against `F`: coins `m + A.coins` (`NUPPT.exists_split m`, the
first `m n` coins are `r`), on `⟨1^n, ⟨i, y⟩⟩` it calls `A` once on `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`
(`NUPPT.exists_comp`, `NUPPT.exists_seq`) and returns the first component of the answer
(`pairFstD`). Then `(F.glPad m).invProbAt A n ≤ F.invProbAt B n`: unfold both `uexp` over
`Gen`'s coins (`OneWay.uexp_mono`), split the inner `uprob` over `D_i × ({0,1}^{m n} × A.Coins n)`
against `D_i × B.Coins n` by `uprob_comp_equiv` on `splitCoins`, and `uprob_mono`: a decoded
answer `(x', r')` with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)`
(`pairEncode_injective`). `Negligible.mono` with `h.hard B`. -/
theorem OneWay.glPad {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).OneWay := by
  obtain ⟨δ, hδ, hS⟩ := h.sampleClose
  refine ⟨⟨δ, hδ, fun n r => ?_⟩, fun A => ?_⟩
  · have key := statClose_glPadSampler F m (F.glPad m henc).sample rfl (glPad_sample_runAtL m henc)
      hS n r _ (henc n r default)
    simp only [glPad_decD_eq] at key ⊢
    exact key
  · refine (h.hard (glPadCollInvMachine A m)).mono ⟨0, fun n _ => ?_⟩
    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
    have key := glPad_invProbAt_le F m A n (fun r => (F.encD (F.index n r) default).length)
      (fun r => henc n r default)
    unfold Collection.invProbAt at key ⊢
    simp only [glPad_decD_eq]
    exact key

/-- **`⟨x, r⟩` is hard-core for the padded collection** ([PS10, Theorem 87.3], collection form,
second clause; inventory Thm-87.3.coll, needed by Theorem 104.4): if `F` is a collection of
one-way functions with encoding length `m(n)` at generated indices, then
`h_i(x, r) = ⟨encD_i x, r⟩` is a hard-core predicate for `F.glPad m` (`Collection.HardCore`).

Repair (run-3 audit P4-2): statement unchanged. The run-2 sketch transferred the cube lemma
`HardcoreBit.invProb_guessInverter` to `D_i` by "identifying `D_i` with `{0,1}^{m n}` through
the injective encoding"; that step is invalid — the image of `encD_i` is in general a strict
subset of the cube (`Z_N^*`, `QR_N`), the uniform `x ∈ D_i` is not a uniform cube element and
the predictor's behaviour off the image is uncontrolled. The transfer is replaced by the
encoded-domain lemma `HardcoreBit.invProb_guessInverter_enc_pad`
(`Asymptotic/GoldreichLevinDomain.lean`), stated for `x` uniform on an arbitrary finite type
with an arbitrary encoding into `{0,1}^m`.

**Proof sketch.** *Easy:* `⟨i, ⟨a, b⟩⟩ ↦ ipFun ⟨padToLen a b, b⟩` — pad `a = encD_i x` to the
length of `b = r` and apply the inner-product evaluator (`exists_glBitCollEvaluator`,
`Asymptotic/HardCoreGLColl.lean`). *Hard:* `glColl_negligible` with the padding length
`L n r = |encD_i(default)| = m(n)` (`henc`) and the one-wayness of the padded collection
(`OneWay.glPad`, its inversion experiment rewritten by `glPad_decD_eq`): by contradiction,
`not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ E_r[Pr[A(1^n, ⟨i, ⟨f_i x, r⟩⟩) = ⟨encD_i x, r⟩]]`
infinitely often; the good indices (`HardcoreBit.half_le_uprob_threshold`) have per-index
success `≥ 1/2 + n^{−c}/2`, where `HardcoreBit.invProb_guessInverter_enc_pad` with
`enc := padFin (m n) ∘ encD_i` and the hard-wired `k(n) = size (8 m(n) n^{2c})` (`glKc`) makes
the recovery procedure of [PS10, Algorithm 89.6] output `encD_i x` with probability
`≥ ε/(4·2^{k(n)})`, `ε = n^{−c}/2`; the inverter `glCollMachine` (the recovery machine `glMachine`
on the pre-processed predictor `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`, output `⟨x', r⟩`) realises it
(`glColl_uprob_le`); averaging over the good indices (`HardcoreBit.uprob_mul_le_uexp`) gives
inversion probability `≥ ε²/(4·2^{k(n)})`, inverse polynomial infinitely often, contradicting
`(OneWay.glPad m henc h).hard`. -/
theorem OneWay.glPad_hardCore {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).HardCore F.glBit := by
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨H, hH, hHx⟩ := exists_glBitCollEvaluator F
    exact ⟨H, hH, fun i x => hHx i x.1 x.2⟩
  · have hmax : ∀ x : ℝ, x ≤ 1 / 2 + max 0 (x - 1 / 2) := fun x => by
      linarith [le_max_right (0 : ℝ) (x - 1 / 2)]
    refine ⟨_, glColl_negligible F m (fun n r => (F.encD (F.index n r) default).length)
      (fun n r => henc n r default) henc A (fun B => ?_), fun n => hmax _⟩
    have key := (OneWay.glPad m henc h).hard B
    unfold Collection.invProbAt at key
    simp only [glPad_decD_eq] at key
    exact key

end Collection

/-- **Goldreich–Levin for collections** ([PS10, Theorem 87.3], the collection form the text
uses for Theorem 104.4 and Chapter 4): for a collection `F` of one-way functions with
encoding length `m(n)` at generated indices, `g_i(x, r) = (f_i(x), r)` is a collection of
one-way functions and `⟨x, r⟩` is hard-core for it. -/
theorem goldreich_levin_coll {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).OneWay ∧ (F.glPad m henc).HardCore F.glBit :=
  ⟨Collection.OneWay.glPad m henc h, Collection.OneWay.glPad_hardCore m henc h⟩

/-- The padded collection of a collection of permutations is a collection of permutations
[PS10, Theorem 87.3, "(OWP)"]: `g_i = perm_i × id` on `D_i × {0,1}^{|encD_i default|}`. -/
noncomputable def PermCollection.glPad (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
    PermCollection :=
  { P.toCollection.glPad m henc with
    perm := fun i => (P.perm i).prodCongr (Equiv.refl _)
    f_perm := fun i z => by simp [Collection.glPad, P.f_perm] }

/-- Unfolding: the underlying collection of `P.glPad m henc` is `P.toCollection.glPad m henc`. -/
theorem PermCollection.glPad_toCollection (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
    (P.glPad m henc).toCollection = P.toCollection.glPad m henc := rfl

/-- **The padded permutation collection is one-way** when the original is (collection form of
[PS10, Theorem 87.3] for Definition 55.1). -/
theorem PermCollection.OneWay.glPad {P : PermCollection} (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (h : P.OneWay) : (P.glPad m henc).OneWay :=
  Collection.OneWay.glPad m henc h

/-- **`⟨x, r⟩` is hard-core for the padded permutation collection**. -/
theorem PermCollection.OneWay.glPad_hardCore {P : PermCollection} (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (h : P.OneWay) : (P.glPad m henc).toCollection.HardCore P.glBit :=
  Collection.OneWay.glPad_hardCore m henc h

/-- The padded collection of a collection of trapdoor permutations is a collection of
trapdoor permutations [PS10, Theorem 87.3 for Definition 56.1, as used in Theorem 104.4]:
`Inv'(1^n, ⟨t, ⟨y, r⟩⟩) = ⟨Inv(1^n, ⟨t, y⟩), r⟩`.

**Proof sketch** (of `inv_spec`). Unfold the activation of the `ofPolyTimeUniform` machine
(`NUPPT.output_ofPolyTime`, the layout projections); `T.inv` is uniform so its activation is
its output on the layout with empty advice; `T.inv_spec` decodes the first component to
`(perm i).symm y.1` and `decodeFin_ofFn` the second to `y.2`. -/
noncomputable def TrapdoorCollection.glPad (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    TrapdoorCollection :=
  { T.toPermCollection.glPad m henc with
    inv := NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins
    inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
    inv_spec := fun n r y s => by
      have hspec := T.inv_spec n r y.1 s
      simp only [NUPPT.runAt, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime, glPadInvFun,
        NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
        pairFstD_pairEncode, pairSndD_pairEncode, PermCollection.glPad, Collection.glPad,
        pairDecode_pairEncode, decodeFin_ofFn, T.inv_uniform n] at hspec ⊢
      rw [hspec]
      rfl }

/-- Unfolding: the underlying permutation collection of `T.glPad m henc` is
`T.toPermCollection.glPad m henc`. -/
theorem TrapdoorCollection.glPad_toPermCollection (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    (T.glPad m henc).toPermCollection = T.toPermCollection.glPad m henc := rfl

/-- **The padded trapdoor collection is one-way** when the original is ([PS10, Theorem 87.3]
for Definition 56.1 (5)). -/
theorem TrapdoorCollection.OneWay.glPad {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) : (T.glPad m henc).OneWay :=
  Collection.OneWay.glPad m henc h

/-- **`⟨x, r⟩` is hard-core for the padded trapdoor collection**: the hypothesis "trapdoor
permutations with a hard-core predicate" of [PS10, Theorem 104.4] is satisfiable from
trapdoor permutations alone. -/
theorem TrapdoorCollection.OneWay.glPad_hardCore {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) : (T.glPad m henc).toCollection.HardCore T.glBit :=
  Collection.OneWay.glPad_hardCore m henc h

end TCSlib.Cryptography
