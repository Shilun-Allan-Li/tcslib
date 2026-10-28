/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The closure calculus of non-uniform PPTs

The class of non-uniform PPTs is closed under the operations every reduction of
[PS10, ch. 2–4] performs silently (inventory item Claim-26.3, "implicit throughout"):
pre- and post-composition with polynomial-time maps, parameter changes, hard-wiring advice,
using fresh coin segments as data, and sequential composition with fresh coins. Each lemma
here exhibits the composite machine as `Complexity.NUPPT.ofPolyTime` of an FP function of
the raw input `⟨⟨⟨1^n, y⟩, α⟩, r⟩` (foundation decision D2), built from
`NUPPT.polyTimeComputable_output`, the pairing calculus of
`TCSlib.Complexity.ClassNP.PolyTimePairing`, the unary evaluator
`Complexity.polyTimeComputable_unaryPoly` and the typed coin cuts
`polyTimeComputable_pairTakePoly`/`pairDropPoly` of
`TCSlib.Complexity.Randomized.Primitives`; the functional equation is
`NUPPT.runAtL_ofPolyTime` followed by the projection identities of the layout.
`Uniform` is preserved whenever the advice is the given machine's or empty.

The supplier table (DESIGN.md §2.5):

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | projections, `pairEncode`, `comp` |
| `exists_reparam p` | advice `A.advice (p n)`; replace `1^n` by `1^{p n}` (`unaryPoly p`) | `unaryPoly` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩`; cut `A.coins (φ n)` coins | `pairTakePoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `p n`; pass the head as data | `pairTakePoly`, `pairDropPoly` |
| `exists_seq` | cut at `A.coins n`; run `A`, then `B` on `⟨y, a⟩`; advice `⟨α_A, α_B⟩` | both outputs, cuts, pairing |

Not in this file (they are FP-level facts the campaign uses directly): negation and
`[true]`-normalisation of verdicts (`Turing.FinTM.computesFunInTime_ifEq` through
`exists_comp`), branching (`Complexity.polyTimeComputable_ite`), length tests
(`polyTimeComputable_lenEq`/`_lenLe`), and the loop fuel of the repetition lemma
(`TCSlib.Complexity.Randomized.Repetition`).

## Main definitions

* `Complexity.NUPPT.layout`, `NUPPT.inParam`, `NUPPT.inArg`, `NUPPT.inAdvice`,
  `NUPPT.inCoins` — the raw input layout `⟨⟨⟨u, y⟩, α⟩, r⟩` and its four projections.
* `Complexity.NUPPT.combineAdvice` — two advice strings as one, keeping `[]` when both are
  empty (so that sequential composition preserves uniformity).

## Main results

* `Complexity.NUPPT.exists_comp` — closure under polynomial-time pre- and post-processing.
* `Complexity.NUPPT.exists_reparam` — parameter change `n ↦ p(n)` (uniformity preserved).
* `Complexity.NUPPT.exists_reparam_advice` — parameter change along a polynomially bounded
  `φ : ℕ → ℕ`, hard-wiring `1^{φ n}` and the advice at `φ n`; extra coins unread.
* `Complexity.NUPPT.exists_withAdvice` — hard-wiring an extra polynomial-length advice.
* `Complexity.NUPPT.exists_split` — the first `p(n)` coins passed as data.
* `Complexity.NUPPT.exists_seq` — sequential composition with input pass-through and fresh
  coins (the "sunglass" composition of [Gar26]'s reductions, at the machine level).
* `Complexity.NUPPT.Computes.polyTimeComputable` — a PPT computing `f` with probability one
  gives `f ∘ advInput` as a polynomial-time function (coins hard-wired to `1^{coins n}`).
* `Complexity.NUPPT.polyTimeComputable_layout` and the projection lemmas — the FP calculus of
  the layout.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of (non-uniform) p.p.t. machines used implicitly throughout.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete reductions these machines package).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, closure of FP under composition.)
-/

namespace Complexity

open Turing

namespace NUPPT

/-! ### The raw input layout and its projections -/

/-- The raw machine input `⟨⟨⟨u, y⟩, α⟩, r⟩`: unary parameter `u`, argument `y`, advice `α`,
coins `r` (`runAtL n y r` is `output (layout 1^n y (advice n) r)`). -/
def layout (u y α r : List Bool) : List Bool := pairEncode (pairEncode (pairEncode u y) α) r

/-- The unary-parameter slot of a raw input. -/
def inParam (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD z))

/-- The argument slot of a raw input. -/
def inArg (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD z))

/-- The advice slot of a raw input. -/
def inAdvice (z : List Bool) : List Bool := pairSndD (pairFstD z)

/-- The coin slot of a raw input. -/
def inCoins (z : List Bool) : List Bool := pairSndD z

/-- The parameter slot of a layout. -/
@[simp] theorem inParam_layout (u y α r : List Bool) : inParam (layout u y α r) = u := by
  simp [inParam, layout]

/-- The argument slot of a layout. -/
@[simp] theorem inArg_layout (u y α r : List Bool) : inArg (layout u y α r) = y := by
  simp [inArg, layout]

/-- The advice slot of a layout. -/
@[simp] theorem inAdvice_layout (u y α r : List Bool) : inAdvice (layout u y α r) = α := by
  simp [inAdvice, layout]

/-- The coin slot of a layout. -/
@[simp] theorem inCoins_layout (u y α r : List Bool) : inCoins (layout u y α r) = r := by
  simp [inCoins, layout]

/-- An activation is the output on the layout `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
theorem runAtL_eq_output_layout (A : NUPPT) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (layout (List.replicate n true) y (A.advice n) r) := rfl

/-- The parameter projection is polynomial-time. -/
theorem polyTimeComputable_inParam : PolyTimeComputable inParam :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)

/-- The argument projection is polynomial-time. -/
theorem polyTimeComputable_inArg : PolyTimeComputable inArg :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)

/-- The advice projection is polynomial-time. -/
theorem polyTimeComputable_inAdvice : PolyTimeComputable inAdvice :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The coin projection is polynomial-time. -/
theorem polyTimeComputable_inCoins : PolyTimeComputable inCoins :=
  polyTimeComputable_pairSndD

/-- Assembling a layout from four polynomial-time functions is polynomial-time
(three applications of `PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_layout {f₁ f₂ f₃ f₄ : List Bool → List Bool}
    (h₁ : PolyTimeComputable f₁) (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃)
    (h₄ : PolyTimeComputable f₄) :
    PolyTimeComputable fun z => layout (f₁ z) (f₂ z) (f₃ z) (f₄ z) :=
  ((h₁.pairEncode h₂).pairEncode h₃).pairEncode h₄

/-- Composition of polynomial-time functions, in applied form. -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-! ### Combined advice -/

/-- Two advice strings as one: `⟨a, b⟩`, except that two empty strings combine to `[]`
(so that composing uniform machines gives a uniform machine). Decoded by `pairFstD` and
`pairSndD`, which return `[]` on `[]`. -/
def combineAdvice (a b : List Bool) : List Bool :=
  if a = [] ∧ b = [] then [] else pairEncode a b

/-- Decoding the first combined advice string. -/
@[simp] theorem pairFstD_combineAdvice (a b : List Bool) : pairFstD (combineAdvice a b) = a := by
  unfold combineAdvice
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

/-- Decoding the second combined advice string. -/
@[simp] theorem pairSndD_combineAdvice (a b : List Bool) : pairSndD (combineAdvice a b) = b := by
  unfold combineAdvice
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

/-- Two empty advice strings combine to the empty string. -/
theorem combineAdvice_nil : combineAdvice [] [] = [] := by
  simp [combineAdvice]

/-- The combined advice has length at most `2|a| + 2 + |b|`. -/
theorem length_combineAdvice_le (a b : List Bool) :
    (combineAdvice a b).length ≤ 2 * a.length + 2 + b.length := by
  unfold combineAdvice
  split_ifs
  · simp
  · rw [length_pairEncode]

/-! ### The closure catalogue -/

/-- **Closure under polynomial-time pre- and post-processing** [PS10, §2.1, implicit;
Claim-26.3 (a), (b)]: for an `NUPPT` `A` and polynomial-time `pre`, `post` there is an
`NUPPT` `B` with the same coins and advice that computes `post (A(1^n, pre y; r))`.

**Proof sketch.** The raw function is
`z ↦ post (A.output (layout (inParam z) (pre (inArg z)) (inAdvice z) (inCoins z)))`, polynomial-time
by `polyTimeComputable_layout`, `PolyTimeComputable.comp`, `NUPPT.polyTimeComputable_output`,
`hpre`, `hpost`; `B := ofPolyTime` of it with `A`'s coins and advice. On the layout
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` the projections return the slots (`runAtL_ofPolyTime`, the
`pairFstD_pairEncode`/`pairSndD_pairEncode` identities), giving `post (A.runAtL n (pre y) r)`. -/
theorem exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
  have hF := ptc_comp hpost (ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam (ptc_comp hpre polyTimeComputable_inArg)
      polyTimeComputable_inAdvice polyTimeComputable_inCoins))
  refine ⟨ofPolyTime hF A.coins A.adv A.advice A.advice_length, rfl, rfl, rfl, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Parameter change `n ↦ p(n)`** [Claim-26.3, implicit]: for an `NUPPT` `A` and a syntactic
polynomial `p` there is an `NUPPT` `B` with coins `A.coins.subst p` that at parameter `n`
behaves as `A` at parameter `p(n)`; `B` is uniform when `A` is (the prefix `1^{p(n)}` is
computed, not hard-wired).

**Proof sketch.** Advice `A.advice (p n)` of length `≤ (A.adv.subst p).eval n`
(`PolyExpr.eval_subst`); the raw function replaces the parameter slot `1^n` by
`1^{p(|1^n|)} = 1^{p n}` (`polyTimeComputable_unaryPoly p` on `inParam`) and re-pairs
(`polyTimeComputable_layout`), then applies `A.output`; the equation is `runAtL_ofPolyTime`
plus the projection identities and `List.length_replicate`. -/
theorem exists_reparam (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r := by
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout
      (ptc_comp (polyTimeComputable_unaryPoly p) polyTimeComputable_inParam)
      polyTimeComputable_inArg polyTimeComputable_inAdvice polyTimeComputable_inCoins)
  have hadv : ∀ n, (A.advice (p.eval n)).length ≤ (A.adv.subst p).eval n := fun n => by
    rw [PolyExpr.eval_subst]
    exact A.advice_length _
  refine ⟨ofPolyTime hF (A.coins.subst p) (A.adv.subst p) (fun n => A.advice (p.eval n)) hadv,
    rfl, fun hA n => hA _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Parameter change along an arbitrary polynomially bounded `φ : ℕ → ℕ`** (non-uniform):
for an `NUPPT` `A`, `φ` with `φ n ≤ p n`, there is an `NUPPT` `B` with coins
`A.coins.subst p` that at parameter `n` behaves as `A` at parameter `φ n` on the first
`A.coins (φ n)` coins (extra coins are unread). This is the one place an abstract `ℕ → ℕ`
appears (as a hypothesis with a `PolyExpr` majorant, D9); it serves Lemma 64.3's
`m(n) = n − ⌊log₂ n⌋`, the literal/`1^n` bridges of Definitions 26.1 and 69.4, and the
interdefinability argument of D3/D4.

**Proof sketch.** Advice `⟨1^{φ n}, A.advice (φ n)⟩`, of length
`2 φ n + 2 + |A.advice (φ n)| ≤ 2 p n + 2 + A.adv (p n)` by `hφ`, `advice_length` and
`PolyExpr.eval_mono` — the bound `add (add (mul (const 2) p) (const 2)) (A.adv.subst p)`. The
raw function reads `w := 1^{φ n}` and `α := A.advice (φ n)` from the advice slot
(`pairFstD`/`pairSndD` of `inAdvice`), cuts the coins to `A.coins.eval |w|` bits
(`polyTimeComputable_pairTakePoly A.coins` on `⟨w, inCoins z⟩`), and runs `A.output` on
`layout w (inArg z) α coins'`; `B.coins = A.coins.subst p ≥ A.coins (φ n)` by `eval_mono`, so
the cut reads existing coins. The equation is `runAtL_ofPolyTime` plus the projection
identities. -/
theorem exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n))) := by
  have hw := ptc_comp polyTimeComputable_pairFstD polyTimeComputable_inAdvice
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout hw polyTimeComputable_inArg
      (ptc_comp polyTimeComputable_pairSndD polyTimeComputable_inAdvice)
      (ptc_comp (polyTimeComputable_pairTakePoly A.coins) (hw.pairEncode polyTimeComputable_inCoins)))
  have hadv : ∀ n, (pairEncode (List.replicate (φ n) true) (A.advice (φ n))).length ≤
      (PolyExpr.add (.add (.mul (.const 2) p) (.const 2)) (A.adv.subst p)).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ n
    have h₂ := A.advice_length (φ n)
    have h₃ := A.adv.eval_mono (hφ n)
    omega
  refine ⟨ofPolyTime hF (A.coins.subst p) _
    (fun n => pairEncode (List.replicate (φ n) true) (A.advice (φ n))) hadv, rfl, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, coinLen, layout, inArg, inAdvice, inCoins]

/-- **Hard-wiring advice** [Claim-26.3 (d)]: for an `NUPPT` `A` and a polynomially bounded
family `β n` there is an `NUPPT` `B` with the same coins that computes
`A(1^n, ⟨y, β n⟩; r)` (the reductions of chapters 2–4 hard-wire hybrid indices, worst-case
inputs and the given adversary's advice this way).

**Proof sketch.** Advice `⟨A.advice n, β n⟩` of length `2 A.adv n + 2 + b n`
(`length_pairEncode`); the raw function re-pairs the argument slot with the second half of
the advice slot and runs `A.output` with the first half as advice
(`polyTimeComputable_layout`, projections). -/
theorem exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r := by
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam
      (polyTimeComputable_inArg.pairEncode
        (ptc_comp polyTimeComputable_pairSndD polyTimeComputable_inAdvice))
      (ptc_comp polyTimeComputable_pairFstD polyTimeComputable_inAdvice) polyTimeComputable_inCoins)
  have hadv : ∀ n, (pairEncode (A.advice n) (β n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) b).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := A.advice_length n
    have h₂ := hβ n
    omega
  refine ⟨ofPolyTime hF A.coins _ (fun n => pairEncode (A.advice n) (β n)) hadv, rfl,
    fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Extra coins passed as data** [Claim-26.3 (c)]: for an `NUPPT` `A` and a syntactic
polynomial `p` there is an `NUPPT` `B` with coins `p + A.coins` and `A`'s advice such that
`B(1^n, y; r) = A(1^n, ⟨y, r.take (p n)⟩; r.drop (p n))`: the first `p n` coins become part of
the input (a uniformly random string of length `p n`), the rest are `A`'s coins.

**Proof sketch.** The raw function cuts the coin slot at `p(|1^n|)` with
`polyTimeComputable_pairTakePoly p`/`pairDropPoly p` on `⟨inParam z, inCoins z⟩`, re-pairs the
argument with the head and runs `A.output` with the tail as coins; the equation is
`runAtL_ofPolyTime`, the projection identities and `List.length_replicate`. -/
theorem exists_split (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r =
        A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam
      (polyTimeComputable_inArg.pairEncode (ptc_comp (polyTimeComputable_pairTakePoly p) hcut))
      polyTimeComputable_inAdvice (ptc_comp (polyTimeComputable_pairDropPoly p) hcut))
  refine ⟨ofPolyTime hF (.add p A.coins) A.adv A.advice A.advice_length, rfl, rfl,
    fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Sequential composition with input pass-through and fresh coins** [Claim-26.3 (b), (c),
(e) with one call]: for `NUPPT`s `A`, `B` there is an `NUPPT` `C` with coins
`A.coins + B.coins`, uniform when both are, computing
`B(1^n, ⟨y, A(1^n, y; r₁)⟩; r₂)` where `r = r₁ ++ r₂` is cut at `A.coins n`. This is the
machine-level form of the "sunglass" reduction `D' := D ∘ (sampler)` of [Gar26] used by
Lemma 71.5 (`Indist.push`) and every two-stage reduction.

**Proof sketch.** Advice `combineAdvice (A.advice n) (B.advice n)` of length
`≤ 2 A.adv n + 2 + B.adv n` (`length_combineAdvice_le`), equal to `[]` when both are empty
(`combineAdvice_nil`, so uniformity is preserved). The raw function cuts the coins at
`A.coins(|1^n|)` (`pairTakePoly`/`pairDropPoly` on `⟨inParam z, inCoins z⟩`), runs `A.output` on
`layout (inParam z) (inArg z) (pairFstD (inAdvice z)) r₁`, pairs the result with the argument
and runs `B.output` on `layout (inParam z) ⟨inArg z, a⟩ (pairSndD (inAdvice z)) r₂`; the
equation is `runAtL_ofPolyTime`, the projection identities, `pairFstD_combineAdvice`,
`pairSndD_combineAdvice` and `List.length_replicate`. -/
theorem exists_seq (A B : NUPPT) :
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hr₁ := ptc_comp (polyTimeComputable_pairTakePoly A.coins) hcut
  have hr₂ := ptc_comp (polyTimeComputable_pairDropPoly A.coins) hcut
  have ha := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam polyTimeComputable_inArg
      (ptc_comp polyTimeComputable_pairFstD polyTimeComputable_inAdvice) hr₁)
  have hF := ptc_comp B.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam (polyTimeComputable_inArg.pairEncode ha)
      (ptc_comp polyTimeComputable_pairSndD polyTimeComputable_inAdvice) hr₂)
  have hadv : ∀ n, (combineAdvice (A.advice n) (B.advice n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) B.adv).eval n := fun n => by
    have h₁ := length_combineAdvice_le (A.advice n) (B.advice n)
    have h₂ := A.advice_length n
    have h₃ := B.advice_length n
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  refine ⟨ofPolyTime hF (.add A.coins B.coins) _
    (fun n => combineAdvice (A.advice n) (B.advice n)) hadv, rfl, fun hA hB n => ?_,
    fun n y r => ?_⟩
  · show combineAdvice (A.advice n) (B.advice n) = []
    rw [hA n, hB n, combineAdvice_nil]
  · rw [runAtL_ofPolyTime]
    simp [runAtL, advInput, coinLen, layout, inParam, inArg, inAdvice, inCoins]

/-- **From "computes with probability one" to FP** [PS10, Definition 24.6; the direction
"a PPT computing `f` gives a polynomial-time evaluator" behind Deviation 3]: if a uniform
`A` computes `f`, then `z ↦ f ⟨1^{|fst z|}, snd z⟩` is polynomial-time computable — run `A`
with the coins hard-wired to the all-`true` string of length `coins n`.

**Proof sketch.** The raw function `z ↦ A.output (layout 1^{|fst z|} (snd z) [] 1^{A.coins |fst z|})`
is polynomial-time (`polyTimeComputable_unary`, `polyTimeComputable_unaryPoly A.coins`,
`polyTimeComputable_layout`); by `Computes` at parameter `|fst z|`, argument `snd z` and
the constant coin string `fun _ => true` (`List.ofFn_const`), it equals
`f (advInput |fst z| (snd z))` everywhere. -/
theorem Computes.polyTimeComputable {A : NUPPT} {f : List Bool → List Bool} (hA : A.Uniform)
    (h : A.Computes f) :
    PolyTimeComputable fun z => f (advInput (pairFstD z).length (pairSndD z)) := by
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout (ptc_comp polyTimeComputable_unary polyTimeComputable_pairFstD)
      polyTimeComputable_pairSndD (polyTimeComputable_const [])
      (ptc_comp (polyTimeComputable_unaryPoly A.coins) polyTimeComputable_pairFstD))
  convert hF using 1
  funext z
  have hz := h (pairFstD z).length (pairSndD z) (fun _ => true)
  have hadv := hA (pairFstD z).length
  simp only [runAt, List.ofFn_const] at hz
  rw [← hz]
  simp [layout, advInput, coinLen, hadv]

end NUPPT

end Complexity
