/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.OneWayYao
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-way functions, asymptotic layer

The one-way function definitions of [PS10, §2.2] and the hardness amplification theorems of
[PS10, §2.4], stated over the machine layer `Complexity.NUPPT` and the typed concrete
experiments of `TCSlib.Cryptography.Foundations.Experiments` (foundation decisions D2, D3,
D5 of `PassShelatChapter2-4Plan.md`).

A *function family* `FunFamily` is `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with syntactic
polynomial lengths (the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p`, parameter =
input length); `FunFamily.invProbAt 𝓕 A n` is the experiment
`Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y]` for the machine `A`, its output decoded as an
`inLen n`-bit string. The three one-wayness notions of [PS10, Definitions 26.1, 27.3, 28.4]
follow — Definition 26.1 in its `1^n` form `FunFamily.WorstCaseOneWay` (headline) and its
literal form `FunFamily.WorstCaseOneWayLit` (`A(f(x))` only), related by
`WorstCaseOneWay.toLit` and `WorstCaseOneWayLit.toParam` (D5, run-3 audit P3-2) —
then the direct product `FunFamily.prod` with the parameters `yaoBlocks`/`yaoRounds`
(`m = 2nq(n)`, `T = 2nm(n)n^c`) of [PS10, §2.4.3], the theorems `weak_to_strong`
[PS10, Theorem 35.1], `strong_prod_two` [PS10, Theorem 35.2], `claim_38_2` (the parameter
instantiation of the concrete `OneWay.yao_amplification_exp` [Gar26, Theorem 2.1]), the sanity
results `FunFamily.StrongOneWay.weak` and `not_strongOneWay_id` (the adversary class is not
vacuous), and `PermFamily`/`OneWayPermutation` [PS10, Theorems 79.4 and 126.4]. Every
asymptotic theorem is proved by (i) instantiating the concrete reduction at every `n`,
(ii) exhibiting the reduction as a `Complexity.NUPPT` by the closure calculus of
`TCSlib/Complexity/Randomized/`, (iii) negligible-function arithmetic (`not_negligible_iff`).

**Deviation:** domains are typed at each parameter (D5): the direct product `𝓕.prod q` is the
family at parameter `n` with input length `q(n)·inLen(n)` and its adversaries receive `1^n`
where the text's adversary of `f'` receives `1^{n·m(n)}`; the two are interderivable
(`1^{n·m(n)}` is computed from `1^n` by `polyTimeComputable_unaryPoly`, and `n` is recovered
from `n·m(n)` by a polynomial search, `m` being monotone), so the classes coincide. The
deviations of `Easy`, `invProbAt` and `WeakOneWay` are recorded on the declarations.

## Main definitions

* `TCSlib.Cryptography.FunFamily` (`Easy`, `invProbAt`, `ofString`, `LengthRegular`, `blocks`,
  `prod`); `FunFamily.StrongOneWay`, `FunFamily.WeakOneWay`, `FunFamily.WorstCaseOneWay`
  (`1^n` form, headline) and `FunFamily.WorstCaseOneWayLit` (literal form)
  [PS10, Definitions 27.3, 28.4, 26.1].
* `TCSlib.Cryptography.yaoBlocks`, `yaoRounds` — `m = 2nq(n)`, `T = 2nm(n)n^c` [PS10, §2.4.3].
* `TCSlib.Cryptography.PermFamily`, `TCSlib.Cryptography.OneWayPermutation`.

## Main results

* `TCSlib.Cryptography.weak_to_strong` [PS10, Theorem 35.1], `strong_prod_two`
  [PS10, Theorem 35.2], `claim_38_2` (parameter instantiation, [PS10, §2.4.3]),
  `OneWay.invProb_prodFun_le_yaoTry` (concrete one-call planting, lemma C2 of the inventory).
* `TCSlib.Cryptography.FunFamily.StrongOneWay.weak`, `TCSlib.Cryptography.not_strongOneWay_id`
  — sanity and non-vacuity.
* `TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit`,
  `TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam` — the two forms of
  [PS10, Definition 26.1] (always / for injective `outLen`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Function families -/

/-- A family `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with explicit polynomial lengths: the
typed reading (D5) of the textbook `f : {0,1}* → {0,1}*` at security parameter `n`
[PS10, §2.2]. -/
structure FunFamily where
  /-- The input length at parameter `n`. -/
  inLen : PolyExpr
  /-- The output length at parameter `n`. -/
  outLen : PolyExpr
  /-- The function at parameter `n`. -/
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily

/-- `𝓕` is *easy to compute*: a polynomial-time string function computes `f n x` from
`⟨1^n, x⟩` [PS10, Definitions 26.1 (1) and 27.3 (1)].

**Deviation:** `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead
of a PPT computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`). -/
def Easy (𝓕 : FunFamily) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)

/-- The inversion probability of the machine `A` against `𝓕` at parameter `n`:
`Pr[x ← {0,1}^{inLen n}; y ← f(x); r : f(A(1^n, y; r)) = y]` with the output of `A` decoded as
an `inLen n`-bit string [PS10, Definitions 27.3 and 28.4, the displayed experiment].

**Deviation:** `inverter`: wrong-length output = failure (D5). -/
noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))

/-- `𝓕` is a *strong one-way function*: easy to compute, and every non-uniform PPT inverts it
with negligible probability [PS10, Definition 27.3]. -/
structure StrongOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: negligible inversion probability for every `A`. -/
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n

/-- `𝓕` is a *weak one-way function*: easy to compute, and there is a polynomial `q` such
that every non-uniform PPT inverts it with probability at most `1 - 1/q(n)` for all
sufficiently large `n` [PS10, Definition 28.4].

**Deviation:** `WeakOneWay`: `0 < q n` made explicit (`1 - 1/0 = 1` would make the clause
vacuous). -/
structure WeakOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert with probability `1 - 1/q(n)`. -/
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)

/-- `𝓕` is a *worst-case one-way function*: easy to compute, and no non-uniform PPT inverts
it on every input with probability one [PS10, Definition 26.1], in the `1^n` form: the
adversary receives `1^n` and `f(x)` (`inverter`, D5) and must return an `inLen n`-bit
preimage. This is the headline form of the definition; the literal form (the adversary
receives `f(x)` only) is `WorstCaseOneWayLit`, and the two are related by
`WorstCaseOneWay.toLit` (always) and `WorstCaseOneWayLit.toParam` (injective `outLen`), as
`Ensemble.Indist`/`Ensemble.IndistLit` for [PS10, Definition 69.4].

Repair (run-3 audit P3-2): the frozen headline was the literal form (now `WorstCaseOneWayLit`),
which is vacuously satisfied by length-shrinking families whose output length does not
determine `n` (e.g. the constant family `x ↦ ε`, trivially invertible in the text); the `1^n`
form is now the headline, mirroring D5's treatment of Definition 69.4.

**Deviation:** the adversary receives `1^n` where the text writes `A(f(x))` (D5; the literal
reading is `WorstCaseOneWayLit`); inverses are sought in the domain at the current parameter
(`inverter`, wrong-length output = failure). -/
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(1^n, f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- `𝓕` is a *worst-case one-way function in the literal form* of [PS10, Definition 26.1]:
easy to compute, and no non-uniform PPT inverts it on every input with probability one, the
adversary receiving `f(x)` only (activation at the output length, `inverterLit`, D5) and
returning an `inLen n`-bit preimage.

Repair (run-3 audit P3-2): renamed from `WorstCaseOneWay`; the `1^n` form `WorstCaseOneWay` is
the headline, and `WorstCaseOneWay.toLit`/`WorstCaseOneWayLit.toParam` relate the two.

**Deviation:** satisfied by every length-shrinking family whose output length does not
determine `n` (e.g. the constant family `x ↦ ε` with `inLen = var`, `outLen = 0`), an artefact
of D5's typed inverse: when `|f(x)|` does not determine `n`, the literal adversary cannot know
the required output length `inLen n`. The `1^n` form is the headline; for injective `outLen`
(every family of the text) the two coincide (`toLit`, `toParam`). -/
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- The output length of a string function on inputs of length `n`, read off at `0^n`. -/
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length

/-- The textbook `f : {0,1}* → {0,1}*` with the output length `p`: parameter = input length,
the output padded or truncated to `p(n)` bits (exact when `f` is `LengthRegular f p`). -/
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
  inLen := .var
  outLen := p
  f _ x i := (f (List.ofFn x)).getD i false

/-- `f` is *length-regular* with output length `p`: `|f x| = p(|x|)` for every `x`. -/
def LengthRegular (f : List Bool → List Bool) (p : PolyExpr) : Prop :=
  ∀ x, (f x).length = p.eval x.length

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The direct product `f'_n = (f_n)^{q n}` of [PS10, Theorem 35.1]:
`f'(x₁, …, x_{q(n)}) = (f(x₁), …, f(x_{q(n)}))` on blocks, encoded as concatenations;
`OneWay.prodFun` [Gar26, Theorem 2.1] blockwise. -/
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily where
  inLen := .mul q 𝓕.inLen
  outLen := .mul q 𝓕.outLen
  f n x := (blocks (q.eval n) (𝓕.outLen.eval n)).symm
    (TCSlib.Cryptography.OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x))

/-! ### Unfolding lemmas -/

/-- The inversion probability is nonnegative. -/
theorem invProbAt_nonneg (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 0 ≤ 𝓕.invProbAt A n :=
  invProbOpt_nonneg _ _

/-- The inversion probability is at most one. -/
theorem invProbAt_le_one (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 𝓕.invProbAt A n ≤ 1 :=
  invProbOpt_le_one _ _

/-- The inversion probability unfolded: the probability over `x` and the coins `r` that the
activation `A(1^n, f(x); r)` is the encoding of some `x'` with `f(x') = f(x)`. -/
theorem invProbAt_eq_uprob (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) :
    𝓕.invProbAt A n = uprob fun z : (Fin (𝓕.inLen.eval n) → Bool) × A.Coins n =>
      ∃ x', A.runAt n (List.ofFn (𝓕.f n z.1)) z.2 = List.ofFn x' ∧ 𝓕.f n x' = 𝓕.f n z.1 := by
  unfold invProbAt invProbOpt
  congr 1
  funext z
  simp only [NUPPT.inverter_eq_some_iff]

/-! ### The two forms of Definition 26.1 -/

/-- **The `1^n` form implies the literal form** of [PS10, Definition 26.1] (repair of the
run-3 audit, P3-2; the analogue of `Ensemble.Indist.toLit`): a literal inverter `A`, activated at
the output length `|f(x)| = outLen n`, is the `1^n`-inverter `NUPPT.exists_reparam A outLen`,
so if no `1^n`-inverter succeeds on every input, no literal inverter does.

**Proof sketch.** `NUPPT.exists_reparam A 𝓕.outLen` gives `B` with
`B.runAtL n y r = A.runAtL (outLen n) y r` and `B.coins = A.coins.subst outLen`, so
`B.Coins n ≃ A.Coins (outLen n)` (`PolyExpr.eval_subst`, `finCongr`); `uprob_comp_equiv`
transports the success event, and `NUPPT.inverter`/`NUPPT.inverterLit` unfold to the same
`decodeFin` of the same activation (`List.ofFn_congr`). -/
theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit := by
  refine ⟨h.easy, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨B, hBc, -, hB⟩ := A.exists_reparam 𝓕.outLen
  refine h.hard ⟨B, fun n x => ?_⟩
  have hlen : B.coinLen n = A.coinLen (𝓕.outLen.eval n) := by
    simp only [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
  let e : A.Coins (𝓕.outLen.eval n) ≃ B.Coins n :=
    Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)
  rw [← uprob_comp_equiv e]
  refine (OneWay.uprob_congr fun r => ?_).trans (hA n x)
  have hofn : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen.symm r).symm
  simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]

/-- **The literal form implies the `1^n` form when the output length determines the
parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
and `B.advice n` at the output length and leaves its extra coins unread.

**Proof sketch.** An injective monotone `outLen.eval` (`PolyExpr.eval_mono`) is strictly
monotone (`Monotone.strictMono_of_injective`), so `n ≤ outLen n` (`StrictMono.id_le`) and
`φ m := the n with outLen n = m` (`0` if none) is majorised by `var`.
`NUPPT.exists_reparam_advice B φ var` gives `A` with
`A.runAtL m y r = B.runAtL (φ m) y (r.take (B.coinLen (φ m)))`; at `m = outLen n` we have
`φ m = n` and `A.Coins m ≃ B.Coins n × (Fin (B.coinLen m − B.coinLen n) → Bool)`
(`Fin.appendEquiv`, `finCongr`, `PolyExpr.eval_mono`); `List.ofFn_fin_append` and
`List.take_left'` identify the literal event with the `1^n` event on the first factor
(`uprob_comp_equiv`, `uprob_fst`). -/
theorem WorstCaseOneWayLit.toParam {𝓕 : FunFamily} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay := by
  classical
  refine ⟨h.easy, ?_⟩
  rintro ⟨B, hB⟩
  have hsm : StrictMono 𝓕.outLen.eval := 𝓕.outLen.eval_mono.strictMono_of_injective hinj
  have hle : ∀ n, n ≤ 𝓕.outLen.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, 𝓕.outLen.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (𝓕.outLen.eval n) = n := by
    intro n
    have hm : ∃ n', 𝓕.outLen.eval n' = 𝓕.outLen.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hinj hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := B.exists_reparam_advice φ .var hφ
  refine h.hard ⟨A, fun n x => ?_⟩
  have hAlen : A.coinLen (𝓕.outLen.eval n) =
      B.coinLen n + (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) := by
    have h1 : A.coinLen (𝓕.outLen.eval n) = B.coinLen (𝓕.outLen.eval n) := by
      simp only [NUPPT.coinLen, hAc, PolyExpr.eval_subst, PolyExpr.eval_var]
    have h2 : B.coinLen n ≤ B.coinLen (𝓕.outLen.eval n) := B.coins.eval_mono (hle n)
    omega
  let e : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool) ≃
      A.Coins (𝓕.outLen.eval n) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hAlen.symm) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have key : ∀ z : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool),
      (∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) (e z) = some x' ∧
        𝓕.f n x' = 𝓕.f n x) ↔
      ∃ x', B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) z.1 = some x' ∧
        𝓕.f n x' = 𝓕.f n x := by
    intro z
    have hofn : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hAlen.symm (Fin.append z.1 z.2)).symm
    simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hA, hφn, hofn,
      List.take_left', List.length_ofFn]
  rw [OneWay.uprob_congr key]
  exact (uprob_fst fun r : B.Coins n => ∃ x',
    B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
      𝓕.f n x' = 𝓕.f n x).trans (hB n x)

/-- On a length-regular `f`, the family `ofString f p` is exactly `f` on encoded strings. -/
theorem ofFn_ofString_f {f : List Bool → List Bool} {p : PolyExpr} (hf : LengthRegular f p)
    (n : ℕ) (x : Fin n → Bool) : List.ofFn ((ofString f p).f n x) = f (List.ofFn x) := by
  have hlen : (f (List.ofFn x)).length = p.eval n := by rw [hf, List.length_ofFn]
  refine List.ext_get (by simp [ofString, hlen]) fun i h₁ h₂ => ?_
  simp [ofString, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The identity family is the identity at every parameter. -/
theorem ofString_id_f (n : ℕ) (x : Fin n → Bool) : (ofString id .var).f n x = x := by
  have h := ofFn_ofString_f (f := id) (p := .var) (fun x => by simp) n x
  exact List.ofFn_injective (by simpa using h)

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (blocks q ℓ).symm t k = t k.divNat k.modNat := rfl

/-- The encoding of a tuple of blocks is the concatenation of the encodings of the blocks. -/
theorem ofFn_blocks_symm (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) :
    List.ofFn ((blocks q ℓ).symm t) = (List.ofFn fun i => List.ofFn (t i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  rw [blocks_symm_apply]
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 1
  · refine Fin.ext ?_
    simp only [Fin.coe_divNat]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, zero_add]
  · refine Fin.ext ?_
    simp only [Fin.coe_modNat]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- The input length of the direct product is `q · inLen`. -/
@[simp] theorem prod_inLen (𝓕 : FunFamily) (q : PolyExpr) : (𝓕.prod q).inLen = .mul q 𝓕.inLen :=
  rfl

/-- The output length of the direct product is `q · outLen`. -/
@[simp] theorem prod_outLen (𝓕 : FunFamily) (q : PolyExpr) :
    (𝓕.prod q).outLen = .mul q 𝓕.outLen := rfl

/-- The direct product unfolded: `prodFun` between the block bijections. -/
theorem prod_f (𝓕 : FunFamily) (q : PolyExpr) (n : ℕ) (x : Fin (q.eval n * 𝓕.inLen.eval n) → Bool) :
    (𝓕.prod q).f n x = (blocks (q.eval n) (𝓕.outLen.eval n)).symm
      (OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x)) := rfl

/-- The inversion probability of the direct product is the concrete `invProbOpt` of
`OneWay.prodFun (f n) (q n)` against the inverter that encodes its challenge tuple by
`blocks` and decodes its answer: the bridge from `𝓕.prod q` to [Gar26, Theorem 2.1].

**Proof sketch.** Reindex the uniform input `x : {0,1}^{q·ℓ}` by the bijection `blocks`
(`uprob_comp_equiv` on the first coordinate); `f'` is `blocks⁻¹ ∘ prodFun ∘ blocks` by
`prod_f`, and `blocks⁻¹` is injective, so the success events coincide pointwise. -/
theorem invProbAt_prod_eq (𝓕 : FunFamily) (q : PolyExpr) (A : NUPPT) (n : ℕ) :
    (𝓕.prod q).invProbAt A n =
      invProbOpt (OneWay.prodFun (𝓕.f n) (q.eval n)) fun ys r =>
        (A.inverter n (q.eval n * 𝓕.inLen.eval n) (q.eval n * 𝓕.outLen.eval n)
          ((blocks (q.eval n) (𝓕.outLen.eval n)).symm ys) r).map (blocks (q.eval n) (𝓕.inLen.eval n)) := by
  unfold invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (blocks (q.eval n) (𝓕.inLen.eval n)) (Equiv.refl _))]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq, prod_f,
    Option.map_eq_some_iff]
  apply propext
  constructor
  · rintro ⟨x', hx', hf⟩
    refine ⟨blocks _ _ x', ⟨x', hx', rfl⟩, ?_⟩
    have := congrArg (blocks (q.eval n) (𝓕.outLen.eval n)) hf
    simpa using this
  · rintro ⟨t, ⟨x', hx', rfl⟩, hf⟩
    exact ⟨x', hx', by simp [hf]⟩

/-- **The direct product is easy to compute.** If `𝓕` is easy then so is `𝓕.prod q`
[PS10, Theorem 35.1, "`f'` is easy to compute"].

**Proof sketch.** Let `F` be the evaluator of `𝓕`. The evaluator of `𝓕.prod q` is the
blockwise evaluator `OneWay.exists_prodEval F inLen q` (an instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word `⟨⟨1^n, cnt⟩, rest⟩`:
while the unary counter `cnt` is shorter than `1^{q(n)}` a round emits `F ⟨1^n, rest.take (inLen n)⟩`
and drops `inLen n` bits, afterwards it emits `[]`; `q` is evaluated at the state-word length
`≥ n`, so exactly `q(n)` rounds emit). Its specification gives the concatenation over `i < q(n)`
of `F ⟨1^n, block i⟩`, which is the concatenation of `List.ofFn (f n (blocks x i))`
(`ofFn_blocks_symm`, the hypothesis on `F`). -/
theorem Easy.prod {𝓕 : FunFamily} (h : 𝓕.Easy) (q : PolyExpr) : (𝓕.prod q).Easy := by
  obtain ⟨F, hF, hFx⟩ := h
  obtain ⟨F', hF', hspec⟩ := OneWay.exists_prodEval hF 𝓕.inLen q
  refine ⟨F', hF', fun n x => ?_⟩
  rw [NUPPT.advInput, hspec, prod_f, ofFn_blocks_symm]
  congr 2
  funext i
  exact hFx n (blocks (q.eval n) (𝓕.inLen.eval n) x i)

end FunFamily

/-! ## Yao's parameters and the concrete one-call reduction -/

/-- The number of blocks `m = 2 n q(n)` of [PS10, §2.4.3] ("we pick `m = 2nq(n)`"), as a
syntactic polynomial. -/
def yaoBlocks (q : PolyExpr) : PolyExpr := .mul (.const 2) (.mul .var q)

/-- The number of repetitions `T = 2 n m(n) n^c` of the one-call inverter [PS10, §2.4.3, the
definition of `A`]: the text's `2nm²p(n)` with `p(n) = n^c` and one factor `m` saved by the
threshold `θ = μ₀/(2m)` of `OneWay.yao_amplification_exp`. -/
def yaoRounds (q : PolyExpr) (c : ℕ) : PolyExpr :=
  .mul (.const 2) (.mul .var (.mul (yaoBlocks q) (.pow .var c)))

/-- `m(n) = 2 n q(n)`. -/
@[simp] theorem eval_yaoBlocks (q : PolyExpr) (n : ℕ) : (yaoBlocks q).eval n = 2 * (n * q.eval n) :=
  rfl

/-- `T(n) = 2 n m(n) n^c`. -/
@[simp] theorem eval_yaoRounds (q : PolyExpr) (c : ℕ) (n : ℕ) :
    (yaoRounds q c).eval n = 2 * (n * ((yaoBlocks q).eval n * n ^ c)) := rfl

/-- `m(n)` is positive for `n ≥ 1` and positive `q`. -/
theorem yaoBlocks_pos (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) {n : ℕ} (hn : 0 < n) :
    0 < (yaoBlocks q).eval n := by
  simp only [eval_yaoBlocks]
  exact Nat.mul_pos (by norm_num) (Nat.mul_pos hn (hq n))

namespace OneWay

/-- **One-call planting reduction** (lemma C2 of the Chapter 2 inventory, the concrete
content of [PS10, Theorem 35.2]): for every fixed position `i`, the inverter that samples
fresh inputs `xs`, plants the challenge `y` at position `i` of `(f(x₁), …, f(x_q))`, calls `B`
and returns the `i`-th component of the answer (`yaoTry` at the fixed position `i`) inverts
`f` with at least the probability with which `B` inverts `prodFun f q`. [PS10, Theorem 35.2,
proof]; the text's test "`f(a) = u`" is unnecessary for the inequality.

**Proof sketch.** In the planted experiment `(x, xs, r)` the tuple `update xs i x` is uniform
(`OneWay.uprob_update`), so the planted experiment is the direct-product experiment with the
answer projected to position `i`; an inverse of the whole tuple inverts every coordinate
(`uprob_mono`). -/
theorem invProb_prodFun_le_yaoTry {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (i : Fin q) :
    invProb (prodFun f q) B ≤ invProb f fun y c => yaoTry f B y (i, c) := by
  unfold invProb
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r => f (B (prodFun f q xs) r i) = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  simp only [yaoTry]
  rw [h]
  apply uprob_mono
  rintro ⟨xs, r⟩ hxs
  exact congrFun hxs i

end OneWay

/-- Polynomial times `2^{-n}` is eventually below one. -/
private theorem eventually_poly_mul_two_pow_lt_one (p : PolyExpr) :
    ∃ n₀, ∀ n ≥ n₀, (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n < 1 := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  have hneg : Negligible fun n => ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow e).const_mul _
  have hμ : Negligible fun n => (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    refine hneg.mono ⟨1, fun n hn => ?_⟩
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
    have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
      apply pow_le_pow_left₀ (by positivity)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * (2 : ℝ)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
            (by positivity)
      _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) := by push_cast; ring
  obtain ⟨n₀, h⟩ := hμ 0
  refine ⟨n₀, fun n hn => lt_of_le_of_lt (le_abs_self _) ?_⟩
  simpa using h n hn

/-- `e^{-n} ≤ 2^{-n}`. -/
private theorem exp_neg_le_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  exact inv_anti₀ (by norm_num) (by linarith)

/-- **Parameter instantiation** [PS10, §2.4.3, Claim 38.2 of the inventory]: with
`m(n) = 2nq(n)` blocks (`yaoBlocks q`) and `T(n) + 1 = 2nm(n)n^c + 1` repetitions
(`yaoRounds q c`), for all large `n` and every `f`, `B` such that `B` inverts `prodFun f (m n)`
with probability at least `1/n^c`, `yaoInverter f B (T n + 1)` inverts `f` with probability
exceeding `1 - 1/q(n) + (T(n) + 1)·2^{-n}` (the margin is the statistical term of the
rejection-sampled positions that `weak_to_strong` subtracts). The concrete inequality is
`OneWay.yao_amplification_exp` [Gar26, Theorem 2.1].

**Deviation:** the text takes `T = 2nm²p(n)` and the threshold `1/(2m²p(n))`; with the
threshold `μ₀/(2m)` of `yao_amplification_exp` one factor `m` is saved. The statistical margin
is absent from the text (exact sampling of `i ← [m]`).

**Proof sketch.** Apply `OneWay.yao_amplification_exp` with `α' := 1/q(n) ≤ 1`, `q := m(n)`
(so `α' m(n) = 2n`), `μ₀ := 1/n^c`, `T' := T(n) + 1` (so `μ₀ T' ≥ 2n m(n)`); it needs
`2e^{-n} < 1/n^c` and yields `invProb f (yaoInverter …) ≥ 1 - 1/(2q(n)) - e^{-n}`. Both this
and the tail bound `e^{-n} + (T(n) + 1) 2^{-n} < 1/(2q(n))` follow from `e^{-n} ≤ 2^{-n}` and
`eventually_poly_mul_two_pow_lt_one` (polynomial times `2^{-n}` is negligible,
`negligible_two_pow_neg`, `Negligible.mul_pow`). `NeZero (m n)` is `yaoBlocks_pos`. -/
theorem claim_38_2 (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) (c : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ {α β ρ : Type} [Fintype α] [Inhabited α] [DecidableEq β] [Fintype ρ]
      [Nonempty ρ] (f : α → β) (B : (Fin ((yaoBlocks q).eval n) → β) → ρ → (Fin ((yaoBlocks q).eval n) → α)),
      1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun f ((yaoBlocks q).eval n)) B →
      1 - 1 / (q.eval n : ℝ) + ((yaoRounds q c).eval n + 1) * (2 : ℝ)⁻¹ ^ n <
        invProb f (OneWay.yaoInverter f B ((yaoRounds q c).eval n + 1)) := by
  obtain ⟨n₁, h₁⟩ := eventually_poly_mul_two_pow_lt_one (.mul (.const 2) (.pow .var c))
  obtain ⟨n₂, h₂⟩ := eventually_poly_mul_two_pow_lt_one
    (.mul (.add (yaoRounds q c) (.const 2)) (.mul (.const 2) q))
  refine ⟨max 1 (max n₁ n₂), fun n hn => ?_⟩
  set m : ℕ := (yaoBlocks q).eval n with hm
  set T : ℕ := (yaoRounds q c).eval n with hT
  intro α β ρ _ _ _ _ _ f B hμ
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (1 : ℝ) ≤ q.eval n := by exact_mod_cast hq n
  have hexp := exp_neg_le_two_pow n
  have hb := h₁ n (le_of_max_le_left (le_of_max_le_right hn))
  have hc := h₂ n (le_of_max_le_right (le_of_max_le_right hn))
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_var,
    PolyExpr.eval_add] at hb hc
  push_cast at hb hc
  have hμ₀ : 2 * Real.exp (-(n : ℝ)) < 1 / (n : ℝ) ^ c := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 2⁻¹ by norm_num) n, pow_pos (show (0:ℝ) < n by linarith) c]
  haveI : NeZero m := ⟨(yaoBlocks_pos q hq hn1).ne'⟩
  have hmR : (m : ℝ) = 2 * (n * q.eval n) := by rw [hm, eval_yaoBlocks]; push_cast; ring
  have hTR : (T : ℝ) = 2 * (n * (m * (n : ℝ) ^ c)) := by rw [hT, eval_yaoRounds]; push_cast; ring
  have hα₁ : 1 / (q.eval n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hqR
  have hq' : 2 * (n : ℝ) ≤ 1 / (q.eval n : ℝ) * (m : ℝ) := by
    have : 1 / (q.eval n : ℝ) * (2 * (n * q.eval n)) = 2 * n := by field_simp
    rw [hmR, this]
  have hT' : 2 * (n : ℝ) * (m : ℝ) ≤ 1 / (n : ℝ) ^ c * ((T + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hTR]
    have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    have : 1 / (n : ℝ) ^ c * (2 * (n * (m * (n : ℝ) ^ c)) + 1) = 2 * n * m + 1 / (n : ℝ) ^ c := by
      field_simp
    rw [this]
    linarith [show 0 < 1 / (n : ℝ) ^ c by positivity]
  have hmain := OneWay.yao_amplification_exp f B (n := n) (α' := 1 / (q.eval n : ℝ))
    (μ₀ := 1 / (n : ℝ) ^ c) (T + 1) hα₁ hq' hT' hμ₀ hμ
  have htail : Real.exp (-(n : ℝ)) + ((T : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < 1 / (q.eval n : ℝ) / 2 := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [lt_div_iff₀ (by norm_num), lt_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ## Hardness amplification -/

/-- The block bijection of this file is the one of `OneWayLemmas`/`OneWayYao`. -/
private theorem blocks_eq_blocksE (q ℓ : ℕ) : FunFamily.blocks q ℓ = OneWay.blocksE q ℓ := rfl

/-- **Yao's hardness amplification** [PS10, Theorem 35.1]: for every weak one-way function
`𝓕` there is a polynomial `m` (the proof takes `m(n) = 2nq(n)`, `q` the polynomial of weak
one-wayness) such that the direct product `𝓕.prod m`, `f'(x₁, …, x_{m(n)}) = (f(x₁), …,
f(x_{m(n)}))`, is strongly one-way.

**Deviation:** `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's
`m = 2nq(n)` and a rejection-sampled position (statistical term absorbed). The direct product
is a family at parameter `n` whose adversaries receive `1^n` (module docstring); the text's
`T = 2nm²p(n)` repetitions become `T(n) + 1`, `T(n) = 2nm(n)n^c` (`yaoRounds`).

**Proof sketch.** Let `q_w` be the polynomial of `h.hard` and `m := yaoBlocks q_w`
(`m(n) = 2nq_w(n)`). *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT` and suppose
`fun n => (𝓕.prod m).invProbAt A' n` is not negligible; `not_negligible_iff` gives `c` with
`1/n^c ≤ (𝓕.prod m).invProbAt A' n` for infinitely many `n` (the function is nonnegative,
`invProbAt_nonneg`). Put `T := yaoRounds q_w c`, `k(n) := Nat.size (m(n))` (so
`m(n) ≤ 2^{k(n)} ≤ 2m(n)`, `k(n) ≤ m(n)`) and `ρ := add (mul var m) (add (mul m inLen) A'.coins)`,
the coins of one round: `n` rejection trials of `m(n)` bits (`k(n)` of them read) for the
position, `m(n)` fresh inputs of `inLen(n)` bits, and the coins of `A'`.

*The reduction `A`* (Algorithm 38.5 repeated) is `NUPPT.ofPolyTime` of an FP function of
the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with coins `mul (add T (const 1)) ρ` and advice
`advice n := ⟨A'.advice n, ⟨1^{m n}, ⟨1^{T n}, ⟨1^{k n}, ⟨1^{inLen n}, 1^{A'.coinLen n}⟩⟩⟩⟩⟩`
(length bounded by the `PolyExpr` `2·A'.adv + 2·m + 2·T + 2·m + 2·inLen + 2·A'.coins + 12`,
`eval_mono`; every component but `A'.advice n` is computable from `1^n`, by
`polyTimeComputable_unaryPoly` and `computesFunInTime_lengthBits` for `1^{k n}`, so uniformity
is preserved). It is an instance of `Complexity.polyTimeComputable_iterateFind` with
`R := T`, `P := var` on the state word `w = ⟨⟨⟨1^n, y⟩, advice n⟩, rest⟩`: the step `g` drops
one round of coins (`polyTimeComputable_pairDropPoly ρ` on `⟨1^n, rest⟩`, re-paired by
`polyTimeComputable_layout`; the orbit never grows, so `horbit` holds); the test `acc w` first
checks that `ρ(n)` coins remain (`polyTimeComputable_lenLe` on `⟨1^{ρ n}, rest⟩`,
`polyTimeComputable_unaryPoly ρ`: `R := T` is evaluated at the raw input length `≥ n`, so at
least `T(n) + 1` rounds are run and the rounds without coins fail), cuts the round's coins
(`polyTimeComputable_pairTakePoly ρ`), reads the position
`i := (rejectionSample (m n) (k n) n (first n·m(n) bits, grouped by `blockMap`)).getD 0`
(each `k(n)`-bit trial compared with `1^{m n}` by `polyTimeComputable_lenLe` after unary
conversion, `polyTimeComputable_ite`), evaluates `ỹ_j := F ⟨1^n, x_j⟩` on the `m(n)` fresh
blocks (iteration as in `Easy.prod`), plants `y` at block `i` (`take`/`drop` at the unary
offset `1^{i·outLen n}`, `Turing.FinTM.computesFunInTime_unaryMul`), calls `A'.output` on the
layout `⟨⟨⟨1^n, ỹ⟩, A'.advice n⟩, r'⟩` (`A'.polyTimeComputable_output`,
`polyTimeComputable_layout`), takes block `i` of the answer when its length is `m(n)·inLen(n)`
and `1^{inLen n}` otherwise (`polyTimeComputable_lenEq`, `polyTimeComputable_ite`), and tests
`F ⟨1^n, z_i⟩ = y` (`Complexity.polyTimeComputable_pairEq`); `out w := z_i`; on exhaustion the
`[]` of `iterateFind` is replaced by `1^{inLen n}` (`polyTimeComputable_lenEq`, `_ite`).

*Functional identity.* With the `Inhabited` instance `default := fun _ => true` on
`Fin (inLen n) → Bool`, `B n ỹ r' := blocks ((A'.inverter n _ _ (blocks⁻¹ ỹ) r').getD default)`
and the typed coin sampler `S n : A.Coins n → (Fin (T n + 1) → Fin (m n) × (Fin (m n) → _) × A'.Coins n)`
(per round: position by `(rejectionSample …).getD 0`, inputs by `blocks`, coins verbatim), for
every `y`, `r`: `A.inverter n _ _ y r = some (OneWay.yaoInverter (𝓕.f n) (B n) (T n + 1) y (S n r))`
(`NUPPT.inverter_eq_some_iff`, `runAtL_ofPolyTime`, the `find?` of `iterateFind` against the
`foldr` of `yaoInverter` by induction on the round list, `decodeFin_ofFn`).

*Probability.* `statClose_rejectionSample (m n) (k n) n 0` puts each round's position within
`(1 - m/2^k)^n ≤ (1/2)^n` of uniform (`uprob_rejectionSample_none_le_half_pow`), the other
components are `StatClose.refl`; `StatClose.prod` over the components and the `T n + 1` rounds
(`StatClose.comp_equiv_left` for the coin-string bijection) gives
`StatClose (S n) id ((T n + 1)·(1/2)^n)`, and `StatClose.abs_uprob_sub_le_prod` with the
auxiliary coins `x` yields `𝓕.invProbAt A n ≥ invProb (𝓕.f n) (yaoInverter (𝓕.f n) (B n)
(T n + 1)) - (T n + 1)(1/2)^n` (`invProbAt_eq_uprob`, `invProbOpt_some`).

*Conclusion.* At the infinitely many `n` with `1/n^c ≤ (𝓕.prod m).invProbAt A' n`:
`invProbAt_prod_eq` and `invProbOpt_le_invProb` give `1/n^c ≤ invProb (prodFun (𝓕.f n) (m n)) (B n)`,
so `claim_38_2` (which packages `OneWay.yao_amplification_exp` with `α' = 1/q_w(n)`,
`μ₀ = 1/n^c`, `T' = T n + 1`) gives `𝓕.invProbAt A n > 1 - 1/q_w(n)` for infinitely many
`n`, contradicting `h.hard` for `A` (`∃ n₀, ∀ n ≥ n₀, … ≤ 1 - 1/q_w(n)`).

*Implementation.* The machine, its functional identity and the statistical step are the theorem
`OneWay.exists_yaoReduction` of `TCSlib.Cryptography.Asymptotic.OneWayYao` (sub-machines in
`OneWayLemmas`): the trial length is `kkOf (m n) = ⌊log₂ m(n)⌋ + 1` (carried as `1^{kk}` in the
advice `⟨A'.advice n, 1^{kk}⟩`), each round reads `n·kk` of its `n·m(n)` position bits, and `B n`
is the total inverter `OneWay.yaoB` (block `i` of `A'`'s answer, padded with `true`), which inverts
the direct product at least as often as `A'`. -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q) := by
  obtain ⟨qw, hqw, hhard⟩ := h.hard
  refine ⟨yaoBlocks qw, h.easy.prod _, fun A' => ?_⟩
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  obtain ⟨F, hF, hFx⟩ := h.easy
  have hFe_spec : ∀ n (a : Fin (𝓕.inLen.eval n) → Bool),
      F (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (𝓕.f n a) :=
    fun n a => hFx n a
  have hm : ∀ n, 1 ≤ n → 0 < (yaoBlocks qw).eval n := fun n hn => yaoBlocks_pos qw hqw hn
  -- the reduction machine of Algorithm 38.5
  obtain ⟨A, hA⟩ := OneWay.exists_yaoReduction 𝓕.inLen 𝓕.outLen (yaoBlocks qw) (yaoRounds qw c)
    𝓕.f hF hFe_spec A' hm
  obtain ⟨n₀, hn₀⟩ := hhard A
  obtain ⟨n₁, hn₁⟩ := claim_38_2 qw hqw c
  obtain ⟨n, hn, hlow⟩ := hc (max 1 (max n₀ n₁))
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnn₀ : n₀ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnn₁ : n₁ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hlow
  -- the total inverter `yaoB` inverts the direct product at least as often as `A'`
  have hB : 1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n))
      (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) := by
    refine hlow.trans ?_
    rw [FunFamily.invProbAt_prod_eq]
    unfold invProbOpt invProb
    apply uprob_mono
    rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
    rw [Option.map_eq_some_iff] at hxs'
    obtain ⟨x'', hx'', rfl⟩ := hxs'
    rw [NUPPT.inverter_eq_some_iff, blocks_eq_blocksE] at hx''
    have hyB : OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n
        (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n) xs) r =
        FunFamily.blocks ((yaoBlocks qw).eval n) (𝓕.inLen.eval n) x'' := by
      funext j
      simp only [OneWay.yaoB]
      rw [hx'', OneWay.padTrue_drop_ofFn]
      rfl
    rw [hyB]
    exact hf
  -- the parameter instantiation and the reduction's bound
  have hclaim := @hn₁ n hnn₁ (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.outLen.eval n) → Bool)
    (A'.Coins n) _ ⟨fun _ => true⟩ _ _ _ (𝓕.f n)
    (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) hB
  have hred := hA n hn1
  have hup := hn₀ n hnn₀
  unfold FunFamily.invProbAt at hup
  rw [one_div] at hred
  linarith

/-- `blocks q ℓ x i j` reads position `ℓ·i + j` of `x`. -/
private theorem blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl

/-- Two blocks: the encoding of `blocks⁻¹ t` is `ofFn (t 0) ++ ofFn (t 1)`. -/
private theorem ofFn_blocks_two_symm (ℓ : ℕ) (t : Fin 2 → Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks 2 ℓ).symm t) = List.ofFn (t 0) ++ List.ofFn (t 1) := by
  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]

/-- **The simple security reduction** [PS10, Theorem 35.2]: if `𝓕` is a strong one-way
function then `g(x, y) = (f(x), f(y))`, the direct product with two blocks (input length
`2·inLen(n)`), is a strong one-way function.

**Deviation:** `g` is `𝓕.prod (const 2)` (two blocks of the typed domain), a family at
parameter `n` whose adversaries receive `1^n` rather than `1^{2n}` (module docstring).

**Proof sketch.** *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT`. The reduction `A`
of the text ("choose a random `y`, compute `v ← f(y)`, submit `(u, v)` to `A'`, output `a`")
is `NUPPT.ofPolyTime` of an FP function of the raw input `⟨⟨⟨1^n, u⟩, A'.advice n⟩, r⟩` with
coins `add (mul (const 2) inLen) A'.coins` and advice `A'.advice`: cut the first `2·inLen n`
coins as a fresh pair of blocks whose second block is `y` (`polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly` on `⟨1^n, r⟩`; the first block is the overwritten coordinate of
the planting lemma), evaluate `v := F ⟨1^n, y⟩` with the evaluator of `h.easy`, call `A'.output`
on the layout `⟨⟨⟨1^n, u ++ v⟩, A'.advice n⟩, r'⟩` (`PolyTimeComputable.append`,
`polyTimeComputable_layout`, `A'.polyTimeComputable_output`) and return the first `inLen n`
bits of the answer (`polyTimeComputable_pairTakePoly inLen`; no length test is needed for an
upper bound). Functional identity: `A.runAt n u (xs, r') = (A'.runAt n (u ++ f (xs 1)) r').take (inLen n)`
after reindexing `A.Coins n ≃ (Fin 2 → Fin (inLen n) → Bool) × A'.Coins n` (`blocks`,
`Fin.appendEquiv`, `uprob_comp_equiv`, `ofFn_blocks_symm`). Probability: `invProbAt_prod_eq`
writes `(𝓕.prod 2).invProbAt A' n` as `invProbOpt (prodFun (f n) 2) B'`, the planting lemma
`OneWay.invProbOpt_prodFun_le_yaoTryOpt` at position `0` bounds it by the planted experiment, and
`uprob_mono` (a `2·inLen n`-bit answer of `A'` decodes to the first block of `A`'s answer,
`ofFn_block_eq_take_drop`) gives `(𝓕.prod 2).invProbAt A' n ≤ 𝓕.invProbAt A n`; conclude by
`h.hard A` and `Negligible.mono` (`invProbAt_nonneg`). -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) :
    FunFamily.StrongOneWay (𝓕.prod (.const 2)) := by
  classical
  obtain ⟨F, hF, hFx⟩ := h.easy
  refine ⟨h.easy.prod _, fun A' => ?_⟩
  -- the reduction: cut two fresh blocks, evaluate `f` on the second, plant, call `A'`, return
  -- the first block of the answer
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hxs := (polyTimeComputable_pairTakePoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hr' := (polyTimeComputable_pairDropPoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hy2 := (polyTimeComputable_pairDropPoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hxs)
  have hv := hF.comp (NUPPT.polyTimeComputable_inParam.pairEncode hy2)
  have hout := A'.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inArg.append hv) NUPPT.polyTimeComputable_inAdvice hr')
  have hG := (polyTimeComputable_pairTakePoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hout)
  let A : NUPPT := NUPPT.ofPolyTime hG (.add (.mul (.const 2) 𝓕.inLen) A'.coins) A'.adv A'.advice
    A'.advice_length
  refine (h.hard A).mono ⟨0, fun n _ => ?_⟩
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  set ℓ := 𝓕.inLen.eval n with hℓ
  set f := 𝓕.f n with hf
  -- the coin bijection `(xs, r') ↦ ⟨xs⟩ ++ r'`
  have hlen : 2 * ℓ + A'.coinLen n = A.coinLen n := rfl
  let e : (Fin 2 → Fin ℓ → Bool) × A'.Coins n ≃ A.Coins n :=
    (Equiv.prodCongr (FunFamily.blocks 2 ℓ).symm (Equiv.refl _)).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)))
  have hofn : ∀ (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      List.ofFn (e (xs, r')) = (List.ofFn (xs 0) ++ List.ofFn (xs 1)) ++ List.ofFn r' := by
    intro xs r'
    rw [← ofFn_blocks_two_symm, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen (Fin.append ((FunFamily.blocks 2 ℓ).symm xs) r')).symm
  -- the functional identity of the reduction
  have hrun : ∀ (y : Fin (𝓕.outLen.eval n) → Bool) (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      A.runAt n (List.ofFn y) (e (xs, r')) =
        (A'.runAt n (List.ofFn y ++ List.ofFn (f (xs 1))) r').take ℓ := by
    intro y xs r'
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTime hG _ _ _ _).runAtL n _ _ = _
    rw [NUPPT.runAtL_ofPolyTime]
    simp only [Function.comp, NUPPT.advInput, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
      NUPPT.inCoins, NUPPT.layout, pairFstD_pairEncode, pairSndD_pairEncode, hofn,
      PolyExpr.eval_mul, PolyExpr.eval_const, List.length_replicate]
    have h2 : (List.ofFn (xs 0) ++ List.ofFn (xs 1)).length = 2 * ℓ := by simp; ring
    rw [List.take_left' h2, List.drop_left' h2,
      List.drop_left' (by simp only [List.length_ofFn]; try exact hℓ)]
    have := hFx n (xs 1)
    simp only [NUPPT.advInput] at this
    rw [this]
    rfl
  -- the planting bound
  let B' : (Fin 2 → Fin (𝓕.outLen.eval n) → Bool) → A'.Coins n → Option (Fin 2 → Fin ℓ → Bool) :=
    fun ys r => (A'.inverter n (2 * ℓ) (2 * 𝓕.outLen.eval n)
      ((FunFamily.blocks 2 (𝓕.outLen.eval n)).symm ys) r).map (FunFamily.blocks 2 ℓ)
  have h1 : (𝓕.prod (.const 2)).invProbAt A' n = invProbOpt (OneWay.prodFun f 2) B' :=
    FunFamily.invProbAt_prod_eq 𝓕 (.const 2) A' n
  have h2 := OneWay.invProbOpt_prodFun_le_yaoTryOpt f B' 0
  refine h1.trans_le (h2.trans ?_)
  unfold FunFamily.invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl _) e)]
  apply uprob_mono
  rintro ⟨x, xs, r'⟩ ⟨x', hx', hfx⟩
  refine ⟨x', ?_, hfx⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rw [Option.map_eq_some_iff] at hx'
  obtain ⟨xs', hxs', rfl⟩ := hx'
  simp only [B', Option.map_eq_some_iff] at hxs'
  obtain ⟨x'', hx'', rfl⟩ := hxs'
  rw [NUPPT.inverter_eq_some_iff, ofFn_blocks_two_symm, Function.update_self,
    Function.update_of_ne (by decide), OneWay.prodFun] at hx''
  rw [NUPPT.inverter_eq_some_iff, hrun, hx'']
  have hblk := OneWay.ofFn_block_eq_take_drop x'' 0
  simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero] at hblk
  rw [← hblk]
  rfl

/-- **Strong implies weak** (sanity, [PS10, §2.2, the remark after Definition 28.4]): a strong
one-way function is a weak one-way function with `q = 2`.

**Proof sketch.** Negligibility with `c = 1` gives `invProbAt A n < 1/n ≤ 1/2 = 1 - 1/2` for
all `n ≥ max n₀ 2`. -/
theorem FunFamily.StrongOneWay.weak {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay := by
  refine ⟨h.easy, .const 2, fun _ => by simp, fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.hard A 1
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / (n : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]; exact one_div_le_one_div_of_le (by norm_num) hn2
  simp only [PolyExpr.eval_const, Nat.cast_ofNat]
  linarith [le_abs_self (𝓕.invProbAt A n)]

/-- **The identity is not one-way** (non-vacuity of the adversary class, [PS10, §2.2]): the
machine that returns its argument inverts `FunFamily.ofString id var` with probability one at
every parameter, and the constant `1` is not negligible.

**Proof sketch.** `A := NUPPT.ofPolyTimeUniform polyTimeComputable_inArg (const 0)` returns
`y` on `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (`runAtL_ofPolyTimeUniform`, `inArg_layout`); its inverter
decodes `List.ofFn y` to `some y` (`decodeFin_ofFn`), and `(ofString id var).f n` is the
identity (`ofString_id_f`), so `invProbAt … A n = uprob True = 1`; `Negligible (fun _ => 1)`
fails at `c = 0`. -/
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var) := by
  intro h
  let A : NUPPT := NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inArg (.const 0)
  have hrun : ∀ n (y : List Bool) (r : A.Coins n), A.runAt n y r = y := by
    intro n y r
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inArg (.const 0)).runAtL n y _ = y
    rw [NUPPT.runAtL_ofPolyTimeUniform]; exact NUPPT.inArg_layout _ _ _ _
  have hone : ∀ n, (FunFamily.ofString id .var).invProbAt A n = 1 := by
    intro n
    rw [FunFamily.invProbAt_eq_uprob]
    have hp : (fun z : (Fin ((FunFamily.ofString id .var).inLen.eval n) → Bool) × A.Coins n =>
        ∃ x', A.runAt n (List.ofFn ((FunFamily.ofString id .var).f n z.1)) z.2 = List.ofFn x' ∧
          (FunFamily.ofString id .var).f n x' = (FunFamily.ofString id .var).f n z.1) =
        fun _ => True := by
      funext z
      refine propext ⟨fun _ => trivial, fun _ => ⟨z.1, ?_, rfl⟩⟩
      rw [hrun, FunFamily.ofString_id_f]
    rw [hp, uprob_true]
  obtain ⟨n₀, hn₀⟩ := h.hard A 0
  have := hn₀ n₀ le_rfl
  simp [hone] at this

/-! ## One-way permutations -/

/-- A family of permutations of `{0,1}^n` (the single one-way permutation of
[PS10, Theorems 79.4 and 126.4]; the *collection* of permutations of [PS10, Definition 55.1] is
`PermCollection` in `Asymptotic/Collections.lean`). -/
structure PermFamily where
  /-- The permutation at parameter `n`. -/
  f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)

/-- The function family underlying a permutation family: `inLen = outLen = var`. -/
def PermFamily.toFunFamily (P : PermFamily) : FunFamily where
  inLen := .var
  outLen := .var
  f n := P.f n

/-- `P` is a *one-way permutation* when its underlying family is strongly one-way
[PS10, §2.12 and Theorem 79.4]. -/
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay

/-- The function of a permutation family is the permutation. -/
@[simp] theorem PermFamily.toFunFamily_f (P : PermFamily) (n : ℕ) (x : Fin n → Bool) :
    P.toFunFamily.f n x = P.f n x := rfl

end TCSlib.Cryptography
