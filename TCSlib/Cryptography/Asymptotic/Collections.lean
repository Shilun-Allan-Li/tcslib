/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Complexity.PolyHierarchy.Padding
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Collections of one-way functions, one-way permutations, trapdoor permutations

The *collection* notions of [PS10, §2.5, §2.10, §2.11]: a family `{f_i : D_i → R_i}_{i ∈ I}`
with a PPT index generator `Gen(1^n)`, a PPT domain sampler, a PPT evaluator and the hardness
clause `Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y] ≤ ε(n)`
[PS10, Definition 41.1]; collections of one-way permutations [PS10, Definition 55.1]; trapdoor
permutations with their inverter [PS10, Definition 56.1]; the hard-core predicate for a
collection (the unnumbered collection form of [PS10, Definition 78.3], used by Lemma 84.1,
Theorem 104.4 and Theorem 126.4); and the equivalence with single strong one-way functions
[PS10, Theorem 42.2].

A `Collection` (foundation decisions D3–D5, D10) has string indices `i : List Bool`, at each
index a finite inhabited domain `D i` with an encoding `encD i` and a total decoder `decD i`,
the string function `f i`, two uniform `NUPPT`s `gen` (`Gen(1^n) = ⟨i, t⟩`, `index`/`trap`)
and `sample`, and a polynomial-time evaluator `eval` agreeing with `f` on encoded elements.
The sampler is required to be within a negligible statistical distance of uniform on `D i`
(`SampleClose`, D10), while the hardness experiment `invProbAt` draws the *ideal* uniform
`x ← D_i`: the average over the generator's coins of the probability, over `x ← D_i` and
the adversary's coins, that the decoded answer is a preimage of `f_i(x)`.

Theorem 42.2: (⇐) a strong one-way family `𝓕` gives the collection `FunFamily.toCollection`
with `Gen(1^n) = ⟨1^n, []⟩`, `D_{1^n} = {0,1}^{inLen n}`, `f_{1^n} = f n`, which is one-way
(`FunFamily.StrongOneWay.toCollection_oneWay`, proved); (⇒, the exercise of the text) the
function `g(r₁, r₂) = ⟨i, f_i(x)⟩`, `i = Gen(1^n; r₁)`, `x = Sample(i; r₂)`, is
`Collection.owfFamily`, strongly one-way by `Collection.OneWay.owfFamily_strongOneWay`
(proved: the evaluator and the collection inverter are built in the FP calculus with the
padding evaluator `padStr` of `TCSlib.Cryptography.Asymptotic.CollectionsLemmas`), from which
the headline `Collection.OneWay.exists_strongOneWay` is proved.

**Deviation:** `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible
statistical distance of uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i`
(`uexp` over `Gen`'s coins).

**Deviation:** the adversary of [PS10, Definitions 41.1 (4), 56.1 (5)] is a non-uniform PPT
(the standing convention of [PS10, p. 26]), receives `1^n`, and its answer is decoded by
`decD i` (a non-decoding answer is a failure, D5); "`f(A(1^n, i, y)) = y`" is read as `f_i`;
the bound `e(k)` of Definition 56.1 (5) is `ε(n)`.

Repair (run-3 audit P3-1): the frozen `Collection` did not tie the evaluator to the sampler
on non-canonical strings, so [PS10, Theorem 42.2 ⇒] was unprovable; the membership half of
[PS10, Definition 41.1 (2)] ("returns an element of `D_i`") is now the field
`Collection.sample_spec`, from which `Collection.EvalSampled` (every sampled string decodes and
`eval` agrees with `f` on it) is derived (`Collection.evalSampled`).

## Main definitions

* `TCSlib.Cryptography.Collection` (`sample_spec`, `index`, `trap`, `SampleClose`,
  `invProbAt`), `TCSlib.Cryptography.Collection.OneWay` — collections of one-way functions
  [PS10, Definition 41.1]; `TCSlib.Cryptography.Collection.HardCore` — hard-core predicate
  for a collection [PS10, Definition 78.3, collection form].
* `TCSlib.Cryptography.PermCollection`, `PermCollection.OneWay` [PS10, Definition 55.1];
  `TCSlib.Cryptography.TrapdoorCollection`, `TrapdoorCollection.OneWay`
  [PS10, Definition 56.1].
* `TCSlib.Cryptography.FunFamily.toCollection`, `Complexity.NUPPT.withIndexParam`
  [PS10, Theorem 42.2 ⇐]; `TCSlib.Cryptography.Collection.owfRaw`, `Collection.owfFamily`,
  `Collection.OutLenBound`, `Collection.EvalSampled`, `TCSlib.Cryptography.splitCoins`
  [PS10, Theorem 42.2 ⇒].

## Main results

* `TCSlib.Cryptography.FunFamily.StrongOneWay.toCollection_oneWay`,
  `FunFamily.StrongOneWay.exists_collection_oneWay` — [PS10, Theorem 42.2 ⇐] (proved).
* `TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay` (proved from the explicit
  form), `Collection.OneWay.owfFamily_strongOneWay` — [PS10, Theorem 42.2 ⇒] (proved).
* `TCSlib.Cryptography.ofFn_splitCoins_fst`, `ofFn_splitCoins_snd`, `ofFn_splitCoins_symm` —
  the coin split `splitCoins` is `List.take`/`List.drop` on the encoded coin string.
* `TCSlib.Cryptography.Collection.evalSampled` — honest evaluation on sampled strings, from
  `sample_spec`.
* `TCSlib.Cryptography.Collection.exists_outLenBound`,
  `Collection.padFin_append_true_injective` — `g` has a polynomial, losslessly padded output.
* `TCSlib.Cryptography.TrapdoorCollection.inv_preimage`,
  `TCSlib.Cryptography.PermCollection.f_injective` — sanity for Definitions 55.1 and 56.1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5 Definition 41.1, Theorem 42.2; §2.10 Definition 55.1; §2.11 Definition 56.1;
  §3.3.3 Definition 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Collections -/

/-- A *collection of functions* `{f_i : D_i → R_i}_{i ∈ I}` [PS10, Definition 41.1 (1)–(3)]:
string indices, finite inhabited domains with encoding and total decoder, the string function
`f i`, a uniform `NUPPT` index generator `Gen(1^n) = ⟨i, t⟩` (`t` ignored by plain
collections), a uniform `NUPPT` domain sampler `Sample(1^n, i)` whose outputs at generated
indices are elements of `D_i` on which the evaluator computes `f_i` (`sample_spec`, the
membership half of clause (2)), and a polynomial-time evaluator `eval ⟨i, x⟩ = f i x` on
encoded elements. The uniformity and hardness clauses are the predicates `SampleClose` and
`OneWay`.

Repair (run-3 audit P3-1): the field `sample_spec` was added (see its docstring). -/
structure Collection where
  /-- The domain `D_i` at the index `i`. -/
  D : List Bool → Type
  /-- Every domain is finite ("uniformly random element of `D_i`"). -/
  [fintypeD : ∀ i, Fintype (D i)]
  /-- Every domain is inhabited (the default of a failed decoding). -/
  [inhabitedD : ∀ i, Inhabited (D i)]
  /-- The string encoding of an element of `D_i`. -/
  encD : ∀ i, D i → List Bool
  /-- The total decoder: wrong strings decode to `none`. -/
  decD : ∀ i, List Bool → Option (D i)
  /-- Decoding inverts encoding. -/
  decD_encD : ∀ i x, decD i (encD i x) = some x
  /-- The function `f_i : D_i → {0,1}*`. -/
  f : ∀ i, D i → List Bool
  /-- The index generator `Gen`. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The domain sampler. -/
  sample : NUPPT
  /-- The sampler is a PPT. -/
  sample_uniform : sample.Uniform
  /-- The evaluator on encoded pairs `⟨i, x⟩`. -/
  eval : List Bool → List Bool
  /-- The evaluator is polynomial-time. -/
  eval_poly : PolyTimeComputable eval
  /-- The evaluator computes `f_i` on encoded elements. -/
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  /-- The sampler returns elements of `D_i` [PS10, Definition 41.1 (2), "returns a uniformly
  random element of `D_i`"]: every string it outputs at an index generated by `Gen(1^n)`
  decodes to some `x ∈ D_i`, and the evaluator computes `f_i(x)` on that string.

  Repair (run-3 audit P3-1): this clause was missing from the frozen structure (D10 relaxed
  the *uniformity* of the sampler to `SampleClose`, not the *membership* of its outputs), which
  made [PS10, Theorem 42.2 ⇒] (`Collection.OneWay.exists_strongOneWay`) unprovable: nothing
  tied the sampler's outputs to `D_i` or the evaluator to `f_i` off the canonical encodings. -/
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
      eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) =
        f (pairFstD (gen.runAt n [] r)) x

attribute [instance] Collection.fintypeD Collection.inhabitedD

namespace Collection

/-- The index `i` output by `Gen(1^n; r)`: the first component of `⟨i, t⟩`. -/
def index (F : Collection) (n : ℕ) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)

/-- The trapdoor `t` output by `Gen(1^n; r)`: the second component [PS10, Definition 56.1 (2)]. -/
def trap (F : Collection) (n : ℕ) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)

/-- The domain sampler is within `δ n` of uniform on `D_i` for every index output by
`Gen(1^n)`: the decoded output of `Sample(1^n, i; s)` on uniform coins `s` is `StatClose` to
the uniform element of `D_i` [PS10, Definition 41.1 (2)].

**Deviation:** domain samplers within negligible statistical distance of uniform (D10). -/
def SampleClose (F : Collection) (δ : ℕ → ℝ) : Prop :=
  ∀ n (r : F.gen.Coins n),
    StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s))
      (fun x : F.D (F.index n r) => some x) (δ n)

/-- The inversion experiment of [PS10, Definition 41.1 (4)]:
`Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y]`: the average over the
generator's coins of the probability, over the ideal uniform `x ∈ D_i` and the coins of `A`,
that `A(1^n, ⟨i, y⟩)` decodes to a preimage `x'` of `y` under `f_i`.

**Deviation:** hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins); the
answer is decoded by `decD i` (a non-decoding answer is a failure, D5). -/
noncomputable def invProbAt (F : Collection) (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : F.gen.Coins n =>
    uprob fun z : F.D (F.index n r) × A.Coins n =>
      ∃ x', F.decD (F.index n r)
          (A.runAt n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2) = some x' ∧
        F.f (F.index n r) x' = F.f (F.index n r) z.1

/-- A *collection of one-way functions* [PS10, Definition 41.1]: the sampler is negligibly
close to uniform (clause (2)) and every non-uniform PPT inverts with negligible probability
(clause (4)); clauses (1) and (3) are the data of `Collection`. -/
structure OneWay (F : Collection) : Prop where
  /-- The domain sampler is within a negligible distance of uniform. -/
  sampleClose : ∃ δ : ℕ → ℝ, Negligible δ ∧ F.SampleClose δ
  /-- Hard to invert: negligible inversion probability for every `A`. -/
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n

/-- `{h_i}` is a *hard-core predicate for the collection* `F` (the collection form of
[PS10, Definition 78.3], unnumbered, used by Lemma 84.1, Algorithm 104.3, Theorem 126.4):
`h_i(x)` is polynomial-time computable from `⟨i, x⟩`, and for every non-uniform PPT `A` there
is a negligible `ε` with `Pr[i ← Gen(1^n); x ← D_i : A(1^n, ⟨i, f_i(x)⟩) = h_i(x)] ≤ 1/2 + ε(n)`
for all `n` (average over `Gen`'s coins, ideal uniform `x`).

**Deviation:** the single-function `A(1^n, f(x))` becomes `A(1^n, ⟨i, f_i(x)⟩)` with the
index drawn by `Gen`; the verdict is the string `[true]` (D5). -/
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop :=
  (∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ i x, H (pairEncode i (F.encD i x)) = [h i x]) ∧
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    uexp (fun r : F.gen.Coins n =>
      uprob fun z : F.D (F.index n r) × A.Coins n =>
        A.distinguisherL n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2 = h (F.index n r) z.1)
      ≤ 1 / 2 + ε n

/-! ### Unfolding and sanity lemmas -/

/-- The encoding of `D_i` is injective (it has the left inverse `decD i`). -/
theorem encD_injective (F : Collection) (i : List Bool) : Function.Injective (F.encD i) :=
  fun x y h => Option.some_injective _ ((F.decD_encD i x).symm.trans (by rw [h, F.decD_encD]))

/-- The inversion probability is nonnegative. -/
theorem invProbAt_nonneg (F : Collection) (A : NUPPT) (n : ℕ) : 0 ≤ F.invProbAt A n := by
  unfold invProbAt uexp
  exact div_nonneg (Finset.sum_nonneg fun r _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The inversion probability is at most one. -/
theorem invProbAt_le_one (F : Collection) (A : NUPPT) (n : ℕ) : F.invProbAt A n ≤ 1 := by
  haveI : Nonempty (F.gen.Coins n) := ⟨fun _ => false⟩
  unfold invProbAt
  exact (OneWay.uexp_mono fun r => uprob_le_one _).trans (OneWay.uexp_const 1).le

end Collection

/-! ## Permutations and trapdoor permutations -/

/-- A *collection of permutations* [PS10, Definition 55.1]: every `f_i` is a permutation of
`D_i` (`f_i = encD_i ∘ perm_i`, `perm_i : D_i ≃ D_i`, so `R_i = D_i` up to encoding);
one-wayness is `PermCollection.OneWay`. -/
structure PermCollection extends Collection where
  /-- The permutation of `D_i`. -/
  perm : ∀ i, D i ≃ D i
  /-- `f_i` is the encoded permutation. -/
  f_perm : ∀ i x, f i x = encD i (perm i x)

/-- A *collection of one-way permutations* [PS10, Definition 55.1]: the underlying collection
is one-way. -/
def PermCollection.OneWay (P : PermCollection) : Prop := P.toCollection.OneWay

/-- `f_i` is injective on `D_i`: the composite of the injective encoding and a bijection. -/
theorem PermCollection.f_injective (P : PermCollection) (i : List Bool) :
    Function.Injective (P.f i) := by
  intro x y h
  rw [P.f_perm, P.f_perm] at h
  exact (P.perm i).injective (P.encD_injective i h)

/-- A *collection of trapdoor permutations* [PS10, Definition 56.1 (1)–(4), (6)]: a collection
of permutations with a uniform `NUPPT` inverter `Inv(1^n, ⟨t, y⟩)` that, for every
`⟨i, t⟩ ← Gen(1^n)` and `y ∈ D_i`, decodes to `f_i^{-1}(y)` for every coin string; the
hardness clause (5) is `TrapdoorCollection.OneWay`.

**Deviation:** the inverter receives `1^n` and the trapdoor `t` only, where the text gives it
"`(i, t)` from `Gen`"; the index is recoverable from the trapdoor in every candidate, which
therefore packs it into `t` (RSA's `Gen` outputs `⟨⟨N, e⟩, ⟨N, d⟩⟩` for the text's
`[(N, e), d]`, Rabin's trapdoor `⟨p, q⟩` determines `N`) — run-3 audit P3-5, the literal
`Inv(1^n, ⟨⟨i, t⟩, y⟩)` form was not adopted. "`f_i^{-1}(y)`, `y ∈ R_i`" is
`(perm i).symm y`, `y ∈ D_i` (the range is `D_i` up to encoding). -/
structure TrapdoorCollection extends PermCollection where
  /-- The trapdoor inverter `Inv`. -/
  inv : NUPPT
  /-- `Inv` is a PPT. -/
  inv_uniform : inv.Uniform
  /-- `Inv(1^n, ⟨t, y⟩)` decodes to `f_i^{-1}(y)` for every coin string. -/
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)

/-- A collection of trapdoor permutations that is hard to invert without the trapdoor
[PS10, Definition 56.1 (5)]: the underlying collection is one-way. **Deviation:** the text's
bound "`≤ e(k)`" is `ε(n)` (source error). -/
def TrapdoorCollection.OneWay (T : TrapdoorCollection) : Prop := T.toCollection.OneWay

/-- **The trapdoor inverter wins the inversion game on every `y`** (sanity for
[PS10, Definition 56.1 (6)]): its decoded answer `x'` satisfies `f_i(x') = encD i y`. -/
theorem TrapdoorCollection.inv_preimage (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n)
    (y : T.D (T.index n r)) (s : T.inv.Coins n) :
    ∃ x', T.decD _ (T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s) = some x' ∧
      T.f (T.index n r) x' = T.encD (T.index n r) y :=
  ⟨(T.perm _).symm y, T.inv_spec n r y s, by rw [T.f_perm, Equiv.apply_symm_apply]⟩

/-! ## Theorem 42.2 (⇐): a strong one-way function is a collection -/

/-- The machine `B(1^n, y) = A(1^n, ⟨1^n, y⟩)`: `A` with the unary parameter prepended to its
argument as the index of `FunFamily.toCollection`; same coins, same advice. -/
noncomputable def _root_.Complexity.NUPPT.withIndexParam (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (f := fun z => A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inParam z) (NUPPT.inArg z)) (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg)
      NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    A.coins A.adv A.advice A.advice_length

/-- `withIndexParam` has the coins of `A`. -/
@[simp] theorem _root_.Complexity.NUPPT.coins_withIndexParam (A : NUPPT) :
    A.withIndexParam.coins = A.coins := rfl

/-- The activation of `withIndexParam`: `B(1^n, y; r) = A(1^n, ⟨1^n, y⟩; r)`. -/
theorem _root_.Complexity.NUPPT.withIndexParam_runAt (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : A.withIndexParam.Coins n) :
    A.withIndexParam.runAt n y r = A.runAt n (pairEncode (List.replicate n true) y) r := by
  rw [NUPPT.runAt_eq]
  unfold NUPPT.withIndexParam
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

namespace FunFamily

variable (𝓕 : FunFamily) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
  (hspec : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x))

/-- The index generator of `toCollection` on `1^n`: `⟨1^n, []⟩` (stated on the machine so that
the definition can discharge `sample_spec`). -/
private theorem toCollection_gen_runAt (n : ℕ)
    (r : (NUPPT.ofPolyTimeUniform
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)).Coins n) :
    (NUPPT.ofPolyTimeUniform
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)).runAt n [] r =
      pairEncode (List.replicate n true) [] := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inParam, NUPPT.advInput]

/-- The sampler of `toCollection` returns its coins (stated on the machine so that the
definition can discharge `sample_spec`). -/
private theorem toCollection_sample_runAt (n : ℕ) (i : List Bool)
    (s : (NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen).Coins n) :
    (NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen).runAt n i s = List.ofFn s := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inCoins]

/-- **The collection of a single function family** [PS10, Theorem 42.2 ⇐]: indices `1^n`
(`Gen(1^n) = ⟨1^n, []⟩`, no coins), domains `D_i = {0,1}^{inLen |i|}` encoded by `List.ofFn`
and decoded by `decodeFin`, `f_i = f_{|i|}`, the sampler returning its `inLen n` coins, and
the evaluator `F` of `𝓕.Easy` on `⟨1^{|i|}, x⟩`. The sampler's output `List.ofFn s` decodes to
`s` and `F` computes `f n s` on it (`sample_spec`, by `decodeFin_ofFn` and `hspec`).

**Deviation:** the text's "`I = {0}`, `D_0 = ℕ`" becomes the unary parameter as the index
with the domain `{0,1}^{inLen n}` at `i = 1^n` (the domain must depend on `n`, D5). -/
noncomputable def toCollection : Collection where
  D i := Fin (𝓕.inLen.eval i.length) → Bool
  encD _ x := List.ofFn x
  decD i w := decodeFin (𝓕.inLen.eval i.length) w
  decD_encD _ x := decodeFin_ofFn x
  f i x := List.ofFn (𝓕.f i.length x)
  gen := NUPPT.ofPolyTimeUniform
    (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval z := F (pairEncode (List.replicate (pairFstD z).length true) (pairSndD z))
  eval_poly := hF.comp
    ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  eval_spec i x := by
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    exact hspec i.length x
  sample_spec n r s := by
    rw [toCollection_sample_runAt]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    revert s
    rw [toCollection_gen_runAt, pairFstD_pairEncode, List.length_replicate]
    intro s
    exact ⟨s, decodeFin_ofFn s, hspec n s⟩

/-- The index generated by `toCollection` is `1^n`. -/
theorem toCollection_index (n : ℕ) (r : (𝓕.toCollection F hF hspec).gen.Coins n) :
    (𝓕.toCollection F hF hspec).index n r = List.replicate n true := by
  unfold Collection.index toCollection
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inParam, NUPPT.advInput]

/-- The sampler of `toCollection` returns its coins. -/
theorem toCollection_sample (n : ℕ) (i : List Bool) (s : (𝓕.toCollection F hF hspec).sample.Coins n) :
    (𝓕.toCollection F hF hspec).sample.runAt n i s = List.ofFn s := by
  unfold toCollection
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inCoins]

/-- The sampler of `toCollection` is exactly uniform (`δ = 0`). -/
theorem toCollection_sampleClose : (𝓕.toCollection F hF hspec).SampleClose fun _ => 0 := by
  intro n r
  generalize hidx : (𝓕.toCollection F hF hspec).index n r = i
  have hi : i.length = n := by rw [← hidx, toCollection_index, List.length_replicate]
  subst hi
  have hX : (fun s : (𝓕.toCollection F hF hspec).sample.Coins i.length =>
      (𝓕.toCollection F hF hspec).decD i ((𝓕.toCollection F hF hspec).sample.runAt i.length i s)) =
      fun s => some s := by
    funext s
    rw [toCollection_sample]
    exact decodeFin_ofFn s
  rw [hX]
  exact StatClose.refl _

/-- A string decodes to `x'` iff it is `List.ofFn x'` (private copy, cf. `inverter_eq_some_iff`). -/
private theorem decodeFin_eq_some_iff {ℓ : ℕ} (w : List Bool) (x' : Fin ℓ → Bool) :
    decodeFin ℓ w = some x' ↔ w = List.ofFn x' := by
  constructor
  · intro h
    have hw : w.length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    rw [h, decodeFin_ofFn]

/-- **The inversion experiment of `toCollection` is that of `𝓕`** against the machine
`withIndexParam A`, which prepends the index `1^n` to its argument.

**Proof sketch.** The generator has no coins, so the average is the value at any `r`; there
the index is `1^n` (`toCollection_index`), the domain is `{0,1}^{inLen n}` and the decoder is
`decodeFin`, so the success event is that of `invProbAt_eq_uprob` for `withIndexParam A`
(`withIndexParam_runAt`, `decodeFin_eq_some_iff`, `List.ofFn_inj`). -/
theorem toCollection_invProbAt (A : NUPPT) (n : ℕ) :
    (𝓕.toCollection F hF hspec).invProbAt A n = 𝓕.invProbAt A.withIndexParam n := by
  haveI : Nonempty ((𝓕.toCollection F hF hspec).gen.Coins n) := ⟨fun _ => false⟩
  unfold Collection.invProbAt
  rw [← OneWay.uexp_const (α := (𝓕.toCollection F hF hspec).gen.Coins n)
    (𝓕.invProbAt A.withIndexParam n)]
  congr 1
  funext r
  generalize hidx : (𝓕.toCollection F hF hspec).index n r = i
  have hi : i.length = n := by rw [← hidx, toCollection_index, List.length_replicate]
  subst hi
  rw [toCollection_index] at hidx
  rw [invProbAt_eq_uprob]
  refine OneWay.uprob_congr fun z => ?_
  show (∃ x', decodeFin (𝓕.inLen.eval i.length)
      (A.runAt i.length (pairEncode i (List.ofFn (𝓕.f i.length z.1))) z.2) = some x' ∧
      List.ofFn (𝓕.f i.length x') = List.ofFn (𝓕.f i.length z.1)) ↔ _
  simp only [NUPPT.withIndexParam_runAt, hidx, decodeFin_eq_some_iff, List.ofFn_inj]

/-- **A strong one-way function is a collection of one-way functions**
[PS10, Theorem 42.2 ⇐], explicit form: for every strong one-way family `𝓕` with evaluator
`F`, the collection `𝓕.toCollection F` is one-way.

**Proof sketch.** The sampler is exactly uniform (`toCollection_sampleClose`, `δ = 0`); the
inversion probability is `𝓕.invProbAt (withIndexParam A) n` (`toCollection_invProbAt`),
negligible by `h.hard`. -/
theorem StrongOneWay.toCollection_oneWay (h : 𝓕.StrongOneWay) :
    (𝓕.toCollection F hF hspec).OneWay where
  sampleClose := ⟨fun _ => 0, fun c => ⟨1, fun n hn => by
      rw [abs_zero]
      exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) c)⟩,
    toCollection_sampleClose 𝓕 F hF hspec⟩
  hard A := by
    simpa only [toCollection_invProbAt] using h.hard A.withIndexParam

/-- **A strong one-way function gives a collection of one-way functions**
[PS10, Theorem 42.2 ⇐]: the collection `toCollection` built from the evaluator of `h.easy`. -/
theorem StrongOneWay.exists_collection_oneWay {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    ∃ G : Collection, G.OneWay := by
  obtain ⟨F, hF, hspec⟩ := h.easy
  exact ⟨_, FunFamily.StrongOneWay.toCollection_oneWay 𝓕 F hF hspec h⟩

end FunFamily

/-! ## Theorem 42.2 (⇒): a collection gives a strong one-way function -/

/-- A string of `a + b` bits as an `a`-bit and a `b`-bit string: the coins `(r₁, r₂)` of
[PS10, Theorem 42.2]. -/
def splitCoins (a b : ℕ) : (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The first half of `splitCoins a b r` is the first `a` bits of the encoding of `r`. -/
theorem ofFn_splitCoins_fst (a b : ℕ) (r : Fin (a + b) → Bool) :
    List.ofFn (splitCoins a b r).1 = (List.ofFn r).take a := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_take,
      List.getElem_ofFn]
    simp [splitCoins, Equiv.sumArrowEquivProdArrow, Fin.castAdd, Fin.castLE]

/-- The second half of `splitCoins a b r` is the encoding of `r` after its first `a` bits. -/
theorem ofFn_splitCoins_snd (a b : ℕ) (r : Fin (a + b) → Bool) :
    List.ofFn (splitCoins a b r).2 = (List.ofFn r).drop a := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_drop,
      List.getElem_ofFn]
    simp [splitCoins, Equiv.sumArrowEquivProdArrow, Fin.natAdd]

/-- The encoding of the coin string assembled from two halves is the concatenation of the
encodings of the halves. -/
theorem ofFn_splitCoins_symm (a b : ℕ) (r₁ : Fin a → Bool) (r₂ : Fin b → Bool) :
    List.ofFn ((splitCoins a b).symm (r₁, r₂)) = List.ofFn r₁ ++ List.ofFn r₂ := by
  set r := (splitCoins a b).symm (r₁, r₂) with hr
  have h1 : (splitCoins a b r).1 = r₁ := by rw [hr, Equiv.apply_symm_apply]
  have h2 : (splitCoins a b r).2 = r₂ := by rw [hr, Equiv.apply_symm_apply]
  rw [← h1, ← h2, ofFn_splitCoins_fst, ofFn_splitCoins_snd, List.take_append_drop]

namespace Collection

variable (G : Collection)

/-- The raw string `⟨i, eval ⟨i, w⟩⟩` of the function `g(r₁, r₂)` of [PS10, Theorem 42.2 ⇒],
`i = Gen(1^n; r₁)`, `w = Sample(1^n, i; r₂)` the sampled encoded `x ∈ D_i`; the second
component is `f_i(x)` by `Collection.sample_spec` (`EvalSampled`). -/
def owfRaw (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) : List Bool :=
  pairEncode (G.index n r₁)
    (G.eval (pairEncode (G.index n r₁) (G.sample.runAt n (G.index n r₁) r₂)))

/-- `L` bounds the length of the raw output of `g` strictly (room for the end marker). -/
def OutLenBound (L : PolyExpr) : Prop :=
  ∀ n (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n), (G.owfRaw n r₁ r₂).length < L.eval n

/-- *Honest evaluation on sampled strings*: every string output by the sampler at a
generated index decodes to some `x ∈ D_i` and the evaluator computes `f_i(x)` on it
[PS10, Definition 41.1 (2)–(3)] — the content of the field `Collection.sample_spec`, stated
with `index` (`Collection.evalSampled`); kept as a named predicate for the consumers that
quote it (`PublicKey`). -/
def EvalSampled : Prop :=
  ∀ n (r : G.gen.Coins n) (s : G.sample.Coins n), ∃ x,
    G.decD (G.index n r) (G.sample.runAt n (G.index n r) s) = some x ∧
      G.eval (pairEncode (G.index n r) (G.sample.runAt n (G.index n r) s)) = G.f (G.index n r) x

/-- **Every collection evaluates honestly on sampled strings**: `EvalSampled` is the field
`sample_spec` read through `index` (repair of the run-3 audit, P3-1; previously an
underivable hypothesis). -/
theorem evalSampled : G.EvalSampled := G.sample_spec

/-- **The function `g(r₁, r₂) = ⟨i, f_i(x)⟩`** of [PS10, Theorem 42.2 ⇒, proof idea] as a
family: input length `|r₁| + |r₂|` (the coins of `Gen` and `Sample`), output length `L`, the
raw string followed by the marker `1` and zero-padded to `L n` bits (recovered by
`splitAtLastTrue`).

**Deviation:** explicit output length `L` (D9) and marker padding for a typed output;
`OutLenBound L` holds for a suitable `L` (`exists_outLenBound`). -/
def owfFamily (L : PolyExpr) : FunFamily where
  inLen := .add G.gen.coins G.sample.coins
  outLen := L
  f n r := padFin (L.eval n)
    (G.owfRaw n (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) r).1
      (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) r).2 ++ [true])

/-- The padding of a short string is the string followed by zeros. -/
theorem ofFn_padFin_of_le {ℓ : ℕ} {w : List Bool} (hw : w.length ≤ ℓ) :
    List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_ofFn, padFin, List.getD_eq_getElem?_getD]
  rw [List.getElem_append]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
    simp

/-- **Marker padding is injective** on strings shorter than the padding length: the family
`owfFamily` loses no information about `⟨i, f_i(x)⟩`. -/
theorem padFin_append_true_injective {ℓ : ℕ} {s s' : List Bool} (hs : s.length < ℓ)
    (hs' : s'.length < ℓ) (h : padFin ℓ (s ++ [true]) = padFin ℓ (s' ++ [true])) : s = s' := by
  have h1 := congrArg List.ofFn h
  rw [ofFn_padFin_of_le (by simp; omega), ofFn_padFin_of_le (by simp; omega)] at h1
  have h2 := congrArg splitAtLastTrue h1
  simp only [List.append_assoc, List.singleton_append, PolyHierarchy.splitAtLastTrue_marker,
    Option.some.injEq] at h2
  exact h2

/-- `|A(1^n, y; r)|` is bounded by the time bound at the length
`8n + 14 + 4|y| + 2·adv(n) + coins(n)` of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
theorem _root_.Complexity.NUPPT.length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : A.Coins n) :
    (A.runAt n y r).length ≤
      A.Ct * (8 * n + 14 + 4 * y.length + 2 * A.adv.eval n + A.coins.eval n + 1) ^ A.ct := by
  refine (A.output_length_le _).trans ?_
  unfold NUPPT.timeBound
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have := A.advice_length n
  simp only [length_pairEncode, NUPPT.length_advInput, List.length_ofFn, NUPPT.coinLen]
  omega

/-- The syntactic polynomial bounding `|A(1^n, y)|` when `|y| ≤ Y(n)` (`length_runAt_le`). -/
def _root_.Complexity.NUPPT.runLenPoly (A : NUPPT) (Y : PolyExpr) : PolyExpr :=
  (PolyExpr.normal A.Ct A.ct).subst
    (.add (.add (.mul (.const 8) .var) (.const 14))
      (.add (.mul (.const 4) Y) (.add (.mul (.const 2) A.adv) A.coins)))

/-- Evaluation of `runLenPoly`. -/
theorem _root_.Complexity.NUPPT.eval_runLenPoly (A : NUPPT) (Y : PolyExpr) (n : ℕ) :
    (A.runLenPoly Y).eval n =
      A.Ct * (8 * n + 14 + 4 * Y.eval n + 2 * A.adv.eval n + A.coins.eval n + 1) ^ A.ct := by
  rw [NUPPT.runLenPoly, PolyExpr.eval_subst, PolyExpr.eval_normal]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  ring

/-- `|A(1^n, y)| ≤ runLenPoly A Y (n)` whenever `|y| ≤ Y(n)`. -/
theorem _root_.Complexity.NUPPT.length_runAt_le_runLenPoly (A : NUPPT) {Y : PolyExpr} (n : ℕ)
    {y : List Bool} (hy : y.length ≤ Y.eval n) (r : A.Coins n) :
    (A.runAt n y r).length ≤ (A.runLenPoly Y).eval n := by
  rw [NUPPT.eval_runLenPoly]
  refine (A.length_runAt_le n y r).trans ?_
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- **The output of `g` has polynomial length**: a syntactic polynomial `L` with
`|⟨i, eval ⟨i, w⟩⟩| < L(n)` for all coins, from the time bounds of `Gen`, `Sample` and `eval`.

**Proof sketch.** `|i| ≤ Q₁(n) := runLenPoly Gen 0`, `|w| ≤ Q₂(n) := runLenPoly Sample Q₁`,
`|eval ⟨i, w⟩| ≤ C(2Q₁ + 2 + Q₂ + 1)^c =: Q₃(n)` (constants of `eval_poly.output_length_le`),
and `|⟨i, ·⟩| = 2|i| + 2 + |·|`, so `L := 2Q₁ + 3 + Q₃` works. -/
theorem exists_outLenBound : ∃ L : PolyExpr, G.OutLenBound L := by
  obtain ⟨C, c, hC⟩ := G.eval_poly.output_length_le
  set Q₁ : PolyExpr := G.gen.runLenPoly (.const 0) with hQ₁
  set Q₂ : PolyExpr := G.sample.runLenPoly Q₁ with hQ₂
  set Q₃ : PolyExpr := (PolyExpr.normal C c).subst
    (.add (.add (.mul (.const 2) Q₁) (.const 2)) Q₂) with hQ₃
  refine ⟨.add (.add (.mul (.const 2) Q₁) (.const 3)) Q₃, fun n r₁ r₂ => ?_⟩
  have hi : (G.index n r₁).length ≤ Q₁.eval n :=
    (length_pairFstD_le _).trans (G.gen.length_runAt_le_runLenPoly n (by simp) r₁)
  have hw : (G.sample.runAt n (G.index n r₁) r₂).length ≤ Q₂.eval n :=
    G.sample.length_runAt_le_runLenPoly n hi r₂
  have he : (G.eval (pairEncode (G.index n r₁) (G.sample.runAt n (G.index n r₁) r₂))).length ≤
      Q₃.eval n := by
    refine (hC _).trans ?_
    rw [hQ₃, PolyExpr.eval_subst, PolyExpr.eval_normal]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  simp only [owfRaw, length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-! ### The evaluator of `g` -/

/-- Composition of polynomial-time functions, in applied form (private copy of the helper
of `TCSlib.Complexity.Randomized.Closure`). -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The index `i = Gen(1^n; r₁)` computed from the unary parameter `u = 1^n` and the coin
string `r`: `Gen`'s output on the layout `⟨⟨⟨u, []⟩, []⟩, r.take (gen.coins |u|)⟩`, first
component. -/
private def owfIndexStr (u r : List Bool) : List Bool :=
  pairFstD (G.gen.output (NUPPT.layout u [] [] (r.take (G.gen.coins.eval u.length))))

/-- The raw string `⟨i, eval ⟨i, Sample(1^n, i; r₂)⟩⟩` of `g` computed from `u = 1^n` and the
coin string `r` (`r₂ = r.drop (gen.coins |u|)`, the sampler on the layout
`⟨⟨⟨u, i⟩, []⟩, r₂⟩`): the string form of `owfRaw` (`owfRawStr_eq`). -/
private def owfRawStr (u r : List Bool) : List Bool :=
  pairEncode (G.owfIndexStr u r) (G.eval (pairEncode (G.owfIndexStr u r)
    (G.sample.output (NUPPT.layout u (G.owfIndexStr u r) [] (r.drop (G.gen.coins.eval u.length))))))

/-- The index computation is polynomial-time on `⟨u, r⟩` (`polyTimeComputable_pairTakePoly`,
`NUPPT.polyTimeComputable_layout`, `NUPPT.polyTimeComputable_output`). -/
private theorem owfIndexStr_poly :
    PolyTimeComputable fun z => G.owfIndexStr (pairFstD z) (pairSndD z) :=
  ptc_comp polyTimeComputable_pairFstD (ptc_comp G.gen.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD (polyTimeComputable_const [])
      (polyTimeComputable_const []) (polyTimeComputable_pairTakePoly G.gen.coins)))

/-- The raw string of `g` is polynomial-time on `⟨u, r⟩` (`polyTimeComputable_pairDropPoly`,
the sampler's and the evaluator's output functions, pairing). -/
private theorem owfRawStr_poly :
    PolyTimeComputable fun z => G.owfRawStr (pairFstD z) (pairSndD z) :=
  have hw : PolyTimeComputable fun z => G.sample.output (NUPPT.layout (pairFstD z)
      (G.owfIndexStr (pairFstD z) (pairSndD z)) []
      ((pairSndD z).drop (G.gen.coins.eval (pairFstD z).length))) :=
    ptc_comp G.sample.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD G.owfIndexStr_poly
        (polyTimeComputable_const []) (polyTimeComputable_pairDropPoly G.gen.coins))
  G.owfIndexStr_poly.pairEncode (ptc_comp G.eval_poly (G.owfIndexStr_poly.pairEncode hw))

/-- On `u = 1^n` and the encoded coins `r₁ ++ r₂`, the index computation is `index n r₁`
(`Gen` is uniform, so its advice is `[]`; the cut at `gen.coins n` is `List.take_left'`). -/
private theorem owfIndexStr_eq (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) :
    G.owfIndexStr (List.replicate n true) (List.ofFn r₁ ++ List.ofFn r₂) = G.index n r₁ := by
  unfold owfIndexStr Collection.index NUPPT.runAt NUPPT.layout NUPPT.advInput
  rw [List.length_replicate, List.take_left' (by simp [NUPPT.coinLen]), G.gen_uniform n]

/-- On `u = 1^n` and the encoded coins `r₁ ++ r₂`, the raw string of `g` is `owfRaw n r₁ r₂`
(`Sample` is uniform; the cut at `gen.coins n` is `List.drop_left'`). -/
private theorem owfRawStr_eq (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) :
    G.owfRawStr (List.replicate n true) (List.ofFn r₁ ++ List.ofFn r₂) = G.owfRaw n r₁ r₂ := by
  unfold owfRawStr owfRaw
  rw [owfIndexStr_eq, List.length_replicate, List.drop_left' (by simp [NUPPT.coinLen])]
  unfold NUPPT.runAt NUPPT.layout NUPPT.advInput
  rw [G.sample_uniform n]

/-- **`g` is easy to compute** [PS10, Theorem 42.2 ⇒, "`g` is easy"]: the evaluator on
`⟨1^n, r⟩` pads `owfRawStr 1^n r ++ [true]` to `L n` bits (`polyTimeComputable_padStr`);
its value on `⟨1^n, List.ofFn r⟩` is `List.ofFn (g n r)` by `owfRawStr_eq`,
`ofFn_splitCoins_fst/snd` and `ofFn_padFin_eq_padStr`. -/
private theorem owfFamily_easy (L : PolyExpr) : (G.owfFamily L).Easy := by
  have hF : PolyTimeComputable fun z =>
      padStr L (pairFstD z) (G.owfRawStr (pairFstD z) (pairSndD z) ++ [true]) := by
    have h := ptc_comp (polyTimeComputable_padStr L)
      (polyTimeComputable_pairFstD.pairEncode (G.owfRawStr_poly.append (polyTimeComputable_const [true])))
    convert h using 1
    funext z
    simp
  refine ⟨_, hF, fun n x => ?_⟩
  have hx : List.ofFn x =
      List.ofFn (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) x).1 ++
        List.ofFn (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) x).2 := by
    rw [← ofFn_splitCoins_symm, Prod.mk.eta, Equiv.symm_apply_apply]
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, owfFamily]
  rw [hx, owfRawStr_eq, ← ofFn_padFin_eq_padStr, List.length_replicate]

/-! ### The collection inverter built from an inverter of `g` -/

/-- The raw function of the collection inverter obtained from an inverter `A'` of `g`, on
the layout `⟨⟨⟨u, ⟨i, y⟩⟩, α⟩, ρ⟩`: pad `⟨i, y⟩ ++ [true]` to `L(|u|)` bits (this is
`List.ofFn (g n r)` whenever `⟨i, y⟩ = owfRaw n r₁ r₂`), run `A'` on it with the advice `α`
and the coins `ρ`, drop the first `gen.coins(|u|)` bits of its answer and run the sampler on
the rest at the index `i`. -/
private def collInvRaw (L : PolyExpr) (A' : NUPPT) (z : List Bool) : List Bool :=
  G.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
    ((A'.output (NUPPT.layout (NUPPT.inParam z)
        (padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true])) (NUPPT.inAdvice z)
        (NUPPT.inCoins z))).drop
      (G.gen.coins.eval (NUPPT.inParam z).length)))

/-- The raw inverter function is polynomial-time.

**Proof sketch.** Four compositions in the FP calculus: the padding
`polyTimeComputable_padStr L` on `⟨inParam z, inArg z ++ [true]⟩`; `A'.output`
(`NUPPT.polyTimeComputable_output`) on the layout assembled by
`NUPPT.polyTimeComputable_layout`; the cut `polyTimeComputable_pairDropPoly G.gen.coins` on
`⟨inParam z, answer⟩`; and `Sample`'s output on the layout `⟨⟨⟨u, fst (inArg z)⟩, []⟩, rest⟩`.
Each `convert … using 1; funext; simp` discharges the projection identities
`pairFstD_pairEncode`/`pairSndD_pairEncode`. -/
private theorem collInvRaw_poly (L : PolyExpr) (A' : NUPPT) :
    PolyTimeComputable (G.collInvRaw L A') := by
  have hpad : PolyTimeComputable fun z =>
      padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true]) := by
    have h := ptc_comp (polyTimeComputable_padStr L)
      (NUPPT.polyTimeComputable_inParam.pairEncode
        (NUPPT.polyTimeComputable_inArg.append (polyTimeComputable_const [true])))
    convert h using 1
    funext z
    simp
  have hA : PolyTimeComputable fun z => A'.output (NUPPT.layout (NUPPT.inParam z)
      (padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true])) (NUPPT.inAdvice z)
      (NUPPT.inCoins z)) :=
    ptc_comp A'.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hpad
        NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)
  have hdrop : PolyTimeComputable fun z => (A'.output (NUPPT.layout (NUPPT.inParam z)
      (padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true])) (NUPPT.inAdvice z)
      (NUPPT.inCoins z))).drop (G.gen.coins.eval (NUPPT.inParam z).length) := by
    have h := ptc_comp (polyTimeComputable_pairDropPoly G.gen.coins)
      (NUPPT.polyTimeComputable_inParam.pairEncode hA)
    convert h using 1
    funext z
    simp
  have h := ptc_comp G.sample.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg)
      (polyTimeComputable_const []) hdrop)
  exact h

/-- The collection inverter `A(1^n, ⟨i, y⟩)` built from an inverter `A'` of `g`
[PS10, Theorem 42.2 ⇒, the reduction]: `collInvRaw` packaged as a machine with the coins
and the advice of `A'`. -/
private noncomputable def collInverter (L : PolyExpr) (A' : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (G.collInvRaw_poly L A') A'.coins A'.adv A'.advice A'.advice_length

/-- The activation of the collection inverter: pad, call `A'`, drop `gen.coins n` bits,
sample at the first component of the argument (`Sample` is uniform). -/
private theorem collInverter_runAt (L : PolyExpr) (A' : NUPPT) (n : ℕ) (y : List Bool)
    (ρ : A'.Coins n) :
    (G.collInverter L A').runAt n y ρ =
      G.sample.runAtL n (pairFstD y)
        ((A'.runAt n (padStr L (List.replicate n true) (y ++ [true])) ρ).drop (G.gen.coinLen n)) := by
  have h := NUPPT.runAtL_ofPolyTime (G.collInvRaw_poly L A') A'.coins A'.adv A'.advice
    A'.advice_length n y (List.ofFn ρ)
  rw [NUPPT.runAt_eq]
  refine h.trans ?_
  simp [collInvRaw, NUPPT.runAtL, NUPPT.runAt, NUPPT.advInput, NUPPT.layout, NUPPT.inParam,
    NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins, NUPPT.coinLen, G.sample_uniform n]

/-- Honest evaluation on sampled strings at an index known to equal `i`
(`Collection.evalSampled` transported along `index n r₁ = i`). -/
private theorem exists_decD_of_index_eq {n : ℕ} (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n)
    {i : List Bool} (hi : G.index n r₁ = i) :
    ∃ x : G.D i, G.decD i (G.sample.runAt n i r₂) = some x ∧
      G.eval (pairEncode i (G.sample.runAt n i r₂)) = G.f i x := by
  subst hi
  exact G.evalSampled n r₁ r₂

/-- **Functional identity of the reduction.** If `A'` inverts `g` on the coins
`(r₁, r₂)` — its answer is the encoding of some `z'` with `g n z' = g n (r₁, r₂)` — then the
sampled string at `(r₁, r₂)` decodes to some `x ∈ D_i` (`i = index n r₁`) and the collection
inverter's answer on `⟨i, f_i(x)⟩` decodes to a preimage of `f_i(x)`.

**Proof sketch.** `evalSampled` gives `x` with `owfRaw n r₁ r₂ = ⟨i, f_i(x)⟩`;
`padFin_append_true_injective` (with `OutLenBound`) turns `g n z' = g n (r₁, r₂)` into
`owfRaw n z'₁ z'₂ = owfRaw n r₁ r₂`, whose components give `index n z'₁ = i` and
`eval ⟨i, Sample(i; z'₂)⟩ = f_i(x)`; the inverter's answer is `Sample(i; z'₂)`
(`collInverter_runAt`, `ofFn_padFin_eq_padStr`, `ofFn_splitCoins_snd`), which decodes to an
`x'` with `f_i(x') = eval ⟨i, Sample(i; z'₂)⟩ = f_i(x)` (`exists_decD_of_index_eq`). -/
private theorem collInverter_success (L : PolyExpr) (hL : G.OutLenBound L) (A' : NUPPT)
    (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) (ρ : A'.Coins n)
    (z' : Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool)
    (hz' : A'.runAt n (List.ofFn ((G.owfFamily L).f n
      ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, r₂)))) ρ = List.ofFn z')
    (hg : (G.owfFamily L).f n z' =
      (G.owfFamily L).f n ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, r₂))) :
    ∃ x, G.decD (G.index n r₁) (G.sample.runAt n (G.index n r₁) r₂) = some x ∧
      ∃ x', G.decD (G.index n r₁) ((G.collInverter L A').runAt n
          (pairEncode (G.index n r₁) (G.f (G.index n r₁) x)) ρ) = some x' ∧
        G.f (G.index n r₁) x' = G.f (G.index n r₁) x := by
  obtain ⟨x, hx1, hx2⟩ := G.evalSampled n r₁ r₂
  refine ⟨x, hx1, ?_⟩
  have hraw : G.owfRaw n r₁ r₂ = pairEncode (G.index n r₁) (G.f (G.index n r₁) x) := by
    unfold owfRaw
    rw [hx2]
  have hg' : G.owfRaw n (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').1
      (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2 = G.owfRaw n r₁ r₂ := by
    have h := hg
    simp only [owfFamily, Equiv.apply_symm_apply] at h
    exact padFin_append_true_injective (hL n _ _) (hL n r₁ r₂) h
  have hidx : G.index n (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').1 = G.index n r₁ := by
    have h := congrArg pairFstD hg'
    simpa only [owfRaw, pairFstD_pairEncode] using h
  have hev : G.eval (pairEncode (G.index n r₁) (G.sample.runAt n (G.index n r₁)
      (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2)) = G.f (G.index n r₁) x := by
    have h := congrArg pairSndD hg'
    simp only [owfRaw, pairSndD_pairEncode] at h
    rw [hidx] at h
    rw [h, hx2]
  have hout : (G.collInverter L A').runAt n (pairEncode (G.index n r₁) (G.f (G.index n r₁) x)) ρ =
      G.sample.runAt n (G.index n r₁) (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2 := by
    rw [collInverter_runAt, pairFstD_pairEncode, ← hraw]
    have hpad : padStr L (List.replicate n true) (G.owfRaw n r₁ r₂ ++ [true]) =
        List.ofFn ((G.owfFamily L).f n
          ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, r₂))) := by
      simp only [owfFamily, Equiv.apply_symm_apply]
      rw [← ofFn_padFin_eq_padStr, List.length_replicate]
    rw [hpad, hz', NUPPT.runAt_eq, ← ofFn_splitCoins_snd]
  rw [hout]
  obtain ⟨x', hx'1, hx'2⟩ := G.exists_decD_of_index_eq
    (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').1
    (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2 hidx
  exact ⟨x', hx'1, by rw [← hx'2, hev]⟩

/-- **The fibre inequality.** For a fixed `r₁` (index `i`), the probability over
`(r₂, ρ)` that `A'` inverts `g` is at most the probability over the ideal `(x, ρ)` that the
collection inverter inverts `f_i`, plus the sampler's distance `δ n` from uniform.

**Proof sketch.** `collInverter_success` is a pointwise implication from the `g`-event to
`P (decD i (Sample(i; r₂))) ρ`, where `P o ρ` says that `o = some x` and the inverter wins
on `⟨i, f_i(x)⟩` (`uprob_mono`); `StatClose.abs_uprob_sub_le_prod` with `h.sampleClose`
moves from the sampled `x` to the ideal uniform `x` at the cost `δ n`; on `some x` the event
`P` is the collection event (`uprob_congr`). -/
private theorem fiber_le (L : PolyExpr) (hL : G.OutLenBound L) (A' : NUPPT) {δ : ℕ → ℝ}
    (hδ : G.SampleClose δ) (n : ℕ) (r₁ : G.gen.Coins n) :
    uprob (fun v : G.sample.Coins n × A'.Coins n => ∃ z',
      A'.runAt n (List.ofFn ((G.owfFamily L).f n
        ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1)))) v.2 = List.ofFn z' ∧
      (G.owfFamily L).f n z' =
        (G.owfFamily L).f n ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1))) ≤
    uprob (fun z : G.D (G.index n r₁) × A'.Coins n => ∃ x', G.decD (G.index n r₁)
        ((G.collInverter L A').runAt n (pairEncode (G.index n r₁) (G.f (G.index n r₁) z.1)) z.2) =
          some x' ∧ G.f (G.index n r₁) x' = G.f (G.index n r₁) z.1) + δ n := by
  let P : Option (G.D (G.index n r₁)) → A'.Coins n → Prop := fun o ρ => ∃ x, o = some x ∧
    ∃ x', G.decD (G.index n r₁) ((G.collInverter L A').runAt n
      (pairEncode (G.index n r₁) (G.f (G.index n r₁) x)) ρ) = some x' ∧
      G.f (G.index n r₁) x' = G.f (G.index n r₁) x
  have hclose := (abs_le.1 ((hδ n r₁).abs_uprob_sub_le_prod P)).2
  have h1 : uprob (fun v : G.sample.Coins n × A'.Coins n => ∃ z',
      A'.runAt n (List.ofFn ((G.owfFamily L).f n
        ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1)))) v.2 = List.ofFn z' ∧
      (G.owfFamily L).f n z' =
        (G.owfFamily L).f n ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1))) ≤
      uprob (fun v : G.sample.Coins n × A'.Coins n =>
        P (G.decD (G.index n r₁) (G.sample.runAt n (G.index n r₁) v.1)) v.2) := by
    refine uprob_mono fun v hv => ?_
    obtain ⟨z', hz', hg⟩ := hv
    exact G.collInverter_success L hL A' n r₁ v.1 v.2 z' hz' hg
  have h2 : uprob (fun z : G.D (G.index n r₁) × A'.Coins n => P (some z.1) z.2) =
      uprob (fun z : G.D (G.index n r₁) × A'.Coins n => ∃ x', G.decD (G.index n r₁)
        ((G.collInverter L A').runAt n (pairEncode (G.index n r₁) (G.f (G.index n r₁) z.1)) z.2) =
          some x' ∧ G.f (G.index n r₁) x' = G.f (G.index n r₁) z.1) := by
    refine OneWay.uprob_congr fun z => ?_
    simp only [P, Option.some.injEq, exists_eq_left']
  linarith

/-- **The inversion probability of `g` is at most that of the collection plus the sampling
error**: `(G.owfFamily L).invProbAt A' n ≤ G.invProbAt (collInverter A') n + δ n`.

**Proof sketch.** `invProbAt_eq_uprob`; reindex the uniform input by `splitCoins` and
reassociate (`uprob_comp_equiv`); average over `r₁` (`uprob_prod`); on each fibre apply
`fiber_le`; the right-hand side is `uexp (fun r₁ => ⋯ + δ n)` by `uexp_add`, `uexp_const`. -/
private theorem invProbAt_owfFamily_le (L : PolyExpr) (hL : G.OutLenBound L) (A' : NUPPT)
    {δ : ℕ → ℝ} (hδ : G.SampleClose δ) (n : ℕ) :
    (G.owfFamily L).invProbAt A' n ≤ G.invProbAt (G.collInverter L A') n + δ n := by
  haveI : Nonempty (G.gen.Coins n) := ⟨fun _ => false⟩
  rw [FunFamily.invProbAt_eq_uprob]
  let e : G.gen.Coins n × (G.sample.Coins n × A'.Coins n) ≃
      (Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool) × A'.Coins n :=
    (Equiv.prodAssoc _ _ _).symm.trans
      (Equiv.prodCongr (splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (Equiv.refl _))
  rw [← uprob_comp_equiv e, uprob_prod]
  unfold Collection.invProbAt
  rw [← OneWay.uexp_const (α := G.gen.Coins n) (δ n), ← OneWay.uexp_add]
  exact OneWay.uexp_mono fun r₁ => G.fiber_le L hL A' hδ n r₁

/-- **The collection's function `g` is a strong one-way function** [PS10, Theorem 42.2 ⇒],
explicit form: if `G` is a collection of one-way functions and `L` bounds the output of `g`,
then `G.owfFamily L` is strongly one-way.

Repair (run-3 audit P3-1): the former hypothesis `hG : G.EvalSampled` is dropped — it is
`G.evalSampled`, from the new field `sample_spec`.

**Deviation (Theorem 42.2 ⇒):** the explicit output length `L` (D9).

**Proof sketch.** *Easy.* The evaluator on `⟨1^n, r⟩` is an FP function: cut `r` into
`r₁`/`r₂` (`polyTimeComputable_pairTakePoly`/`_pairDropPoly G.gen.coins`), run `G.gen.output`
on the layout `⟨⟨⟨1^n, []⟩, []⟩, r₁⟩` (`NUPPT.polyTimeComputable_layout`, `gen_uniform`),
project `i` (`pairFstD`), run `G.sample.output` on `⟨⟨⟨1^n, i⟩, []⟩, r₂⟩`, apply `G.eval_poly`
to `⟨i, w⟩`, pair, append the marker `[true]` and `0^{L n}` (`PolyTimeComputable.append`,
`polyTimeComputable_unaryPoly L` mapped to zeros by `polyTimeComputable_blockMap (const 1)`
with the constant `[false]`), keep the first `L n` bits (`polyTimeComputable_pairTakePoly L`
on `⟨1^n, ·⟩`); the result is `List.ofFn (padFin (L n) (owfRaw ++ [true]))` by
`ofFn_padFin_of_le` and `OutLenBound`. *Hard.* Fix `A' : NUPPT`. The reduction
`A(1^n, ⟨i, y⟩; ρ)` (advice and coins of `A'`) pads `⟨i, y⟩ ++ [true]` to `L n` bits as above,
calls `A'.output` on `⟨⟨⟨1^n, t⟩, A'.advice n⟩, ρ⟩`, checks that the answer `z` has length
`gen.coins(n) + sample.coins(n)` (`polyTimeComputable_lenEq`, `_ite`), splits it into
`(r₁', r₂')` and outputs `G.sample.output ⟨⟨⟨1^n, i⟩, []⟩, r₂'⟩`. Functional identity: when
`A'` returns `z` with `g(z) = padFin (L n) (⟨i, y⟩ ++ [true])`, `padFin_append_true_injective`
and `pairEncode_injective` give `index n r₁' = i` and `eval ⟨i, w'⟩ = y` for
`w' := sample(1^n, i; r₂')`, and `G.evalSampled` decodes `w'` to an `x'` with `f_i(x') = y`.
Probability: for fixed `r₁` (index `i`) the `g`-experiment on `(r₂, ρ)` is the collection
experiment on `(x, ρ)` with `x := decD i (sample(i; r₂))` (`G.evalSampled` gives
`y = f_i(x)`), so `uprob_prod` over `r₁`, `uprob_comp_equiv (splitCoins …)`, `uprob_mono` (the
pointwise implication) and `StatClose.abs_uprob_sub_le_prod` with `h.sampleClose` give
`(G.owfFamily L).invProbAt A' n ≤ G.invProbAt A n + δ n` (`invProbAt_eq_uprob`); conclude by
`h.hard A`, `Negligible.add` and `Negligible.mono` (`invProbAt_nonneg`). -/
theorem OneWay.owfFamily_strongOneWay {G : Collection} (h : G.OneWay)
    {L : PolyExpr} (hL : G.OutLenBound L) : (G.owfFamily L).StrongOneWay where
  easy := G.owfFamily_easy L
  hard A' := by
    obtain ⟨δ, hδneg, hδ⟩ := h.sampleClose
    refine Negligible.mono ((h.hard (G.collInverter L A')).add hδneg) ⟨0, fun n _ => ?_⟩
    have hδ0 : 0 ≤ δ n := (hδ n fun _ => false).nonneg
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _),
      abs_of_nonneg (add_nonneg (Collection.invProbAt_nonneg _ _ _) hδ0)]
    exact G.invProbAt_owfFamily_le L hL A' hδ n

/-- **A collection of one-way functions gives a strong one-way function**
[PS10, Theorem 42.2 ⇒, "left as an exercise"]: the function `g(r₁, r₂) = ⟨i, f_i(x)⟩` with
`i = Gen(1^n; r₁)` and `x = Sample(i; r₂)`.

Repair (run-3 audit P3-1): provable from the explicit form once `Collection.sample_spec` ties
the sampler to `D_i` (previously the frozen statement was unprovable from the frozen fields).

**Proof sketch.** Take `L` from `exists_outLenBound G` and `𝓕 := G.owfFamily L`;
`owfFamily_strongOneWay h hL`. -/
theorem OneWay.exists_strongOneWay {F : Collection} (h : F.OneWay) :
    ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay :=
  let ⟨L, hL⟩ := F.exists_outLenBound
  ⟨F.owfFamily L, h.owfFamily_strongOneWay hL⟩

end Collection

end TCSlib.Cryptography
