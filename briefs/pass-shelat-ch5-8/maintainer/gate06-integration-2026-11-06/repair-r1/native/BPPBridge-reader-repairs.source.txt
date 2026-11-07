/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.PolyTimeModel
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From `main`'s BPP verifiers to the ch. 2–4 machines (the S3c bridge)

[PS10, Theorem 180.1] derandomizes `BPP`. Its proof turns a verifier that is fooled by a
pseudorandom generator into a distinguisher for the generator. `BPP` is `main`'s
(`Randomized.InBPP Randomized.polyTimeModel`, after [AB09, Def 7.3]), and the generator's
security quantifies over the ch. 2–4 layer's non-uniform machines (`Complexity.NUPPT`). This
module is the one-way bridge between the two models (decision D-6; route note
`briefs/pass-shelat-ch5-8/design/S3c-bpp-bridge.md`). It edits neither model.

1. **A verifier as a machine** (`verifier_toNUPPT`): an efficient Boolean verifier `M` of `main`'s
   polynomial-time model, with an input sequence `xs n` hard-wired as advice, is a non-uniform
   machine that outputs `[M (xs n) y]` on the string `y`. This is the distinguisher of Thm 180.1's
   proof, with the bad input `x` in its advice.
2. **The two probabilities agree** (`randProb_eq_uprob`): `main`'s counting ratio `randProb` over
   `{0,1}^m`, cast to `ℝ`, is the ch. 2–4 layer's `uprob` over `Fin m → Bool`.
3. **The coin schedule as a syntactic polynomial** (`polyLenExpr`, `eval_polyLenExpr`): `main`'s
   `polyLen a k n = a · (n + 1)^k` is the `PolyExpr` the machines' coin and advice bounds use.

## Main definitions

* `Randomness.polyLenExpr`: `polyLen a k` as a `PolyExpr`.

## Main results

* `Randomness.verifier_toNUPPT`: a verifier with hard-wired inputs is a non-uniform machine.
* `Randomness.randProb_eq_uprob`: the two probability notions agree.
* `Randomness.eval_polyLenExpr`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, Definition 7.3 (`main`'s `BPP`).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity Turing TCSlib.Cryptography

/-- `main`'s coin schedule `polyLen a k = n ↦ a · (n + 1)^k` as a syntactic polynomial. -/
def polyLenExpr (a k : ℕ) : PolyExpr := .mul (.const a) (.pow (.add .var (.const 1)) k)

/-- The coin-schedule expression is the product of `a` and `(n+1)^k` in PolyExpr syntax. -/
theorem polyLenExpr_eq (a k : ℕ) :
    polyLenExpr a k = .mul (.const a) (.pow (.add .var (.const 1)) k) := rfl

/-- The syntactic polynomial evaluates to `main`'s schedule. -/
@[simp] theorem eval_polyLenExpr (a k n : ℕ) :
    (polyLenExpr a k).eval n = Randomized.polyLen a k n := by
  simp only [polyLenExpr_eq, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_add, PolyExpr.eval_var, Randomized.polyLen_eq]

/-- **A verifier of `main`'s polynomial-time model, with hard-wired inputs, is a non-uniform
machine** (the S3c bridge, lemma 1). Let `M` be an efficient Boolean verifier
(`polyTimeModel.Eff (boolVerifier M)`: its true-set and false-set on `⟨x, r⟩` are in `P`), and
`xs n` inputs of length at most `p(n)`. Then there is a machine `D` with advice `xs`, no coins,
that at parameter `n` on the string `y` outputs `[M (xs n) y]`.

**Proof sketch.** The true-set `V₁` of `M` is in `P`, so its indicator is polynomial-time
(`mem_P_iff_polyTimeComputable`). Compose it with the projection
`⟨⟨⟨1^n, y⟩, xs n⟩, r⟩ ↦ ⟨xs n, y⟩` (`inAdvice`, `inArg`, `pairEncode`), and build `D` with
`NUPPT.ofPolyTime`, whose advice field takes the length bound `hxs`. -/
theorem verifier_toNUPPT {M : List Bool → List Bool → Bool}
    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
    (xs : ℕ → List Bool) (p : PolyExpr) (hxs : ∀ n, (xs n).length ≤ p.eval n) :
    ∃ D : NUPPT, D.advice = xs ∧
      ∀ n (y : List Bool) (r : D.Coins n), D.runAt n y r = [M (xs n) y] := by
  obtain ⟨V₁, V₀, h₁, -, hV⟩ :=
    (Randomized.polyTimeModel_eff_iff (Randomized.boolVerifier M)).mp hM
  have hM₁ : ∀ x r, M x r = true ↔ pairEncode x r ∈ V₁ := fun x r => by
    have := (hV x r).1
    simpa [Randomized.boolVerifier_apply] using this
  have hind := mem_P_iff_polyTimeComputable.mp h₁
  have hf₀ := hind.comp
    (NUPPT.polyTimeComputable_inAdvice.pairEncode NUPPT.polyTimeComputable_inArg)
  have hf : PolyTimeComputable fun z =>
      [MultiTapeTM.indicator V₁ (pairEncode (NUPPT.inAdvice z) (NUPPT.inArg z))] := by
    refine (congrArg PolyTimeComputable (?_ : (fun z =>
      [MultiTapeTM.indicator V₁ (pairEncode (NUPPT.inAdvice z) (NUPPT.inArg z))]) = _)).mpr hf₀
    funext z
    simp only [Function.comp_apply]
  refine ⟨NUPPT.ofPolyTime hf (.const 0) p xs hxs,
    NUPPT.advice_ofPolyTime hf (.const 0) p xs hxs, fun n y r => ?_⟩
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.inAdvice_eq, NUPPT.inArg_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.cons.injEq, and_true]
  by_cases h : M (xs n) y = true
  · have hm := (hM₁ _ _).mp h
    simp only [(Randomized.indicator_eq_true_iff).2 hm, h]
  · have hm : pairEncode (xs n) y ∉ V₁ := fun hm => h ((hM₁ _ _).mpr hm)
    simp only [Bool.not_eq_true] at h
    simp only [(Randomized.indicator_eq_false_iff).2 hm, h]

/-- **The two probability notions agree** (the S3c bridge, lemma 2): `main`'s `randProb m A`, the
counting ratio over `{0,1}^m`, is the ch. 2–4 layer's `uprob` over `Fin m → Bool`. -/
theorem randProb_eq_uprob (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    (Randomized.randProb m A : ℝ) = uprob (fun r : Fin m → Bool => A (List.ofFn r)) := by
  rw [uprob_eq_card_filter, Randomized.randProb_eq]
  push_cast
  congr 1
  simp [Fintype.card_bool, Fintype.card_fin]

end TCSlib.Cryptography.Randomness
