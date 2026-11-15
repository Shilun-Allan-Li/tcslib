/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.LearningTheory.PAC
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Randomness.Learning.Sample
import TCSlib.Cryptography.Randomness.Learning.Distinguisher
import TCSlib.Cryptography.Randomness.Learning.Law
import TCSlib.Cryptography.Randomness.Learning.Random
/- DLC-SEAL Randomness_Learning: whole-file closure seal of `TCSlib/Cryptography/Randomness/Learning.lean`, variant A (PolyExpr.eval open), coe (projection coercions open). -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let coeOpen : Bool := true
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
          continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Randomness_Learning: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom functions make an unlearnable concept class

[PS10, §8.1, Theorem 179.1]: if pseudorandom functions exist, there is a p.p.t.-decidable
concept class that no non-uniform p.p.t. learner can learn: given polynomially many labelled uniform
examples, it predicts the label of a fresh uniform point with probability at most `½` plus a
negligible amount.

**The class.** For a PRF family `{f_k}`, `C_k = {x : f_k(x)₁ = 1}`, the first output bit
(`prfConcept`).

**The learner.** An efficient learner is a machine `A` run at parameter `n` on
`⟨labelled sample, x⟩`. Its hypothesis on `x` is whether it outputs `[true]` (`learnerOf`). The
examples are given non-adaptively, as in the source's question. The prediction game and the PAC
notions are those of the information-theoretic layer `TCSlib.LearningTheory.PAC` (S3d layer 1,
[Shilun-Allan-Li/tcslib#194]), at the uniform distribution on `{0,1}^n` and uniform keys.

## Main definitions

* `Randomness.prfConcept`, `Randomness.encodeSample`, `Randomness.learnerOf`.

## Main results

* `Randomness.prfConcept_decidable` (Thm 179.1, part (a), proved): membership is
  polynomial-time decidable given the key.
* `Randomness.predictAdv_prfConcept_negligible` (Thm 179.1, part (b), proved): every efficient
  learner's prediction advantage is negligible.
* `Randomness.not_weakLearnsUnder_prfConcept` (Thm 179.1, part (c), proved from (b) and the PAC
  layer's bridge): no efficient learner weakly PAC-learns the class under the uniform distribution
  with a constant edge `γ` at fixed failure probability `δ < γ`. Amplifying a KV94-style
  weak learner changes the learner and its resources; that amplification and its resource
  bridge are additional results, not a construction already supplied by part (c).

## Contents

This file states the class, the learner and Theorem 179.1, and assembles the proof of part (b)
from the helper modules under `Learning/` (namespace `Randomness.LearnPRF`):
- `Sample`: the learner's input and the last label as polynomial-time functions of the encoded
  tuple of query points and answers (`learnIn`, `lastLabel`);
- `Distinguisher`: the PRF distinguisher built from a learner (`exists_learnDist`);
- `Law`: the prediction game and the distinguisher's acceptance probability as one uniform
  probability (`predictSuccess_eq_uprob`, `gameProb`, `exists_learnDist_acceptProb`);
- `Random`: with a uniform random function the prediction is within `m/2^n` of `½`
  (`abs_gameProb_random_sub_half_le`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity Turing TCSlib.Cryptography TCSlib.LearningTheory.PAC TCSlib.InformationTheory

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))

/-- **The concept class of Theorem 179.1** at parameter `n`: `C_k(x) = f_k(x)₁`, the first output
bit (`false` at `n = 0`). -/
def prfConcept (n : ℕ) (k x : Fin n → Bool) : Bool := (List.ofFn (F n k x)).headD false

/-- The concept value is the first output bit of `F n k x`, with default `false` for an
empty output: `prfConcept F n k x = (List.ofFn (F n k x)).headD false`. -/
theorem prfConcept_eq (n : ℕ) (k x : Fin n → Bool) :
    prfConcept F n k x = (List.ofFn (F n k x)).headD false := rfl

/-- The encoding of a labelled sample for a learner machine: the nested pairs of `⟨x_j, [b_j]⟩`. -/
def encodeSample {n m : ℕ} (S : Fin m → (Fin n → Bool) × Bool) : List Bool :=
  (List.ofFn fun j => pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []

/-- A labelled sample is encoded by folding its list of pairs `⟨x_j, [b_j]⟩` from the right,
with empty terminal word. -/
theorem encodeSample_eq {n m : ℕ} (S : Fin m → (Fin n → Bool) × Bool) :
    encodeSample S =
      (List.ofFn fun j => pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode [] := rfl

/-- **The learner of a machine** `A` at parameter `n` with `m` examples: on the labelled sample `S`
and coins `r`, the hypothesis `x ↦ [A(1^n, ⟨S, x⟩; r) = [true]]`. -/
def learnerOf (A : NUPPT) (n m : ℕ) :
    (Fin m → (Fin n → Bool) × Bool) → A.Coins n → (Fin n → Bool) → Bool :=
  fun S r x => decide (A.runAt n (pairEncode (encodeSample S) (List.ofFn x)) r = [true])

/-- The learner's prediction on `S`, coins `r` and input `x` is the decision whether the
machine run on `⟨encodeSample S, List.ofFn x⟩` outputs `[true]`. -/
theorem learnerOf_eq (A : NUPPT) (n m : ℕ) (S : Fin m → (Fin n → Bool) × Bool)
    (r : A.Coins n) (x : Fin n → Bool) :
    learnerOf A n m S r x =
      decide (A.runAt n (pairEncode (encodeSample S) (List.ofFn x)) r = [true]) := rfl

/-- **Theorem 179.1 (a): the class is p.p.t.-decidable** given the key: the first bit of the PRF's
evaluator decides membership. -/
theorem prfConcept_decidable (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (k x : Fin n → Bool), f (pairEncode (List.ofFn k) (List.ofFn x)) = [prfConcept F n k x] :=
  ⟨fun z => [(E z).headD false], polyTimeComputable_headD.comp hE, fun n k x => by
    simp only [prfConcept, hFE]⟩

/-- **Theorem 179.1 (b): no efficient learner predicts the class** [PS10, Theorem 179.1]: if `F` is
a PRF, then for every non-uniform PPT learner `A` and polynomial number `m` of examples, the
prediction advantage `|Pr[A predicts C_k(x)] − ½|` at uniform `k`, uniform examples and a fresh
uniform `x` is negligible.

**Proof sketch** (the source's, made explicit; the delivered proof).
1. **The distinguisher and the real game.** The next-query machine `D` of
   `LearnPRF.exists_learnDist_acceptProb` takes `m(n) + 1` uniform points from its coins, queries
   its oracle at them (the non-adaptive query chain `MultiMsg.exists_queryChain_nuppt`), labels
   the first `m(n)` with the answers' first bits, runs `A` (with its own coins) on the labelled
   sample and the last point, and accepts when `A`'s prediction equals the last answer's first
   bit. Against any keyed family its acceptance probability is a uniform probability over the
   key, the examples, the coins and the fresh point (`LearnPRF.gameProb`); with `f_k` this is
   the prediction game (`LearnPRF.predictSuccess_eq_uprob`), so
   `predictSuccess = acceptProb (F n) D`. The fresh point may equal an example, in both.
2. **The random function.** With a uniform random function `R`, for `n ≥ 1`: when the last point
   is none of the examples, flipping the first bit of `R` there exchanges winning and losing
   functions, so `D` wins with probability exactly `½`; the last point is an example with
   probability at most `m(n)/2^n` (union bound). So `|acceptProb R D − ½| ≤ m(n)/2^n`
   (`LearnPRF.abs_gameProb_random_sub_half_le`).
3. **The bound.** For `n ≥ 1`, `predictAdv ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n`, which is
   negligible by `PRF.negligible_prfAdv` (budget `m + 1`), `EnsembleLemmas.negligible_polyExpr_mul`
   with `negligible_two_pow_neg`, and `Negligible.add`; the eventual bound gives negligibility
   (`Negligible.mono` from `n = 1`, so `n = 0` needs no case). -/
theorem predictAdv_prfConcept_negligible (hF : PRF F) (A : NUPPT) (m : PolyExpr) :
    Negligible fun n => predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) := by
  obtain ⟨B, hB⟩ := LearnPRF.exists_learnDist_acceptProb A m
  -- The owned learner and concept are the helpers' `learnerFn` and `firstBit`.
  have hL : ∀ n, learnerOf A n (m.eval n) = LearnPRF.learnerFn A n (m.eval n) := fun n => by
    funext S r x
    rw [learnerOf_eq, LearnPRF.learnerFn_eq, encodeSample_eq]
  have hC : ∀ n (k : Fin n → Bool), prfConcept F n k = fun x => LearnPRF.firstBit (F n k x) :=
    fun n k => funext fun x => by rw [prfConcept_eq, LearnPRF.firstBit_eq]
  -- Step 1: the prediction game is the distinguisher's game with `f_k`.
  have hreal : ∀ n, predictSuccess (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) =
      acceptProb (F n) (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) := by
    intro n
    rw [hB, LearnPRF.predictSuccess_eq_uprob, LearnPRF.gameProb_eq, hL]
    simp only [hC]
  -- Step 2: with a random function the acceptance probability is within `m(n)/2^n` of `½`.
  have hrand : ∀ n, 0 < n →
      |acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
          (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) - 1 / 2| ≤
        (m.eval n : ℝ) / 2 ^ n := by
    intro n hn
    rw [hB]
    have h := LearnPRF.abs_gameProb_random_sub_half_le hn (m.eval n)
      (LearnPRF.learnerFn A n (m.eval n))
    rwa [show (fun R : (Fin n → Bool) → (Fin n → Bool) => R) =
      randomFunction (Fin n → Bool) (Fin n → Bool) from
        funext fun R => (randomFunction_apply _ _ R).symm] at h
  -- Step 3: the bound, negligible by PRF security and `m(n)/2^n → 0`.
  have hQ : ∀ n, (PolyExpr.add m (.const 1)).eval n = m.eval n + 1 := fun n => by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  have hprf := hF.negligible_prfAdv B (.add m (.const 1))
  simp only [hQ] at hprf
  have hpow : Negligible fun n => (m.eval n : ℝ) / 2 ^ n := by
    refine (EnsembleLemmas.negligible_polyExpr_mul m negligible_two_pow_neg).mono
      ⟨0, fun n _ => le_of_eq ?_⟩
    rw [inv_pow, div_eq_mul_inv]
  refine (hprf.add hpow).mono ⟨1, fun n hn => ?_⟩
  have h₁ := hrand n (by omega)
  have h₂ := prfAdv_nonneg (F n) (B.toOracleAdversary n n n (m.eval n + 1))
  have h₃ : (0 : ℝ) ≤ (m.eval n : ℝ) / 2 ^ n := by positivity
  rw [predictAdv_eq, hreal, abs_abs, abs_of_nonneg (add_nonneg h₂ h₃), prfAdv_def, distAdv_def]
  calc _ ≤ |acceptProb (F n) (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) -
          acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
            (oracleDist (B.toOracleAdversary n n n (m.eval n + 1)))| +
        |acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
            (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) - 1 / 2| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- **Theorem 179.1 (c): no efficient weak PAC learner** under the uniform distribution: for edges
`δ < γ ≤ ½`, every efficient learner fails to `(γ, δ)`-weakly learn the class from some
parameter on. Proved from part (b) and the PAC layer's `not_weakLearnsUnder_of_predictAdv_le`.

**Proof sketch.** Part (b) eventually bounds the prediction advantage by `1/n`. Since
`γ - δ > 0`, choose a second cutoff beyond which `1/n ≤ (γ - δ)/2`. Above both cutoffs,
the advantage is strictly smaller than the edge required for weak learning, so the PAC
prediction-to-learning bound rules out a weak learner. -/
theorem not_weakLearnsUnder_prfConcept (hF : PRF F) (A : NUPPT) (m : PolyExpr) {γ δ : ℝ}
    (hδγ : δ < γ) (hγ : γ ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ¬ WeakLearnsUnder (FinDist.uniform (Fin n → Bool)) (prfConcept F n)
      (m.eval n) (learnerOf A n (m.eval n)) γ δ := by
  have hneg := predictAdv_prfConcept_negligible F hF A m
  rw [negligible_iff] at hneg
  obtain ⟨n₁, hn₁⟩ := hneg 1
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (2 / (γ - δ))
  refine ⟨max n₁ (n₂ + 1), fun n hn => ?_⟩
  have h1 := hn₁ n (le_trans (le_max_left _ _) hn)
  have hpos : (0 : ℝ) < γ - δ := by linarith
  have hn' : (n₂ : ℝ) + 1 ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]
  have hsmall : 1 / (n : ℝ) ^ 1 ≤ (γ - δ) / 2 := by
    rw [pow_one, div_le_div_iff₀ hnpos (by norm_num)]
    have : 2 / (γ - δ) < n := by linarith
    rw [div_lt_iff₀ hpos] at this
    linarith
  have hadv : predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) ≤ (γ - δ) / 2 :=
    le_trans (le_abs_self _) (le_trans h1.le hsmall)
  exact not_weakLearnsUnder_of_predictAdv_le hadv (by linarith) hγ

end TCSlib.Cryptography.Randomness
