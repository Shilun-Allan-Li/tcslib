/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for ensembles and computational indistinguishability

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.Asymptotic.Ensembles` ([PS10, §3.1.1]: Lemma 71.5, the literal/`1^n`
bridges of Definition 69.4, the multicopy corollary of Lemma 71.6 and the prediction
Lemma 73.8). Everything here is ensemble-free: samplers at one parameter, `Complexity.NUPPT`
machines built by the closure calculus of `TCSlib.Complexity.Randomized.Closure`, and the
statistical-closeness device of `TCSlib.Cryptography.Asymptotic.Sampling`. The file exists
only to keep `Ensembles.lean` within the repository's size limit (workflow §4 (4)); its
declarations live in the inner namespace `TCSlib.Cryptography.EnsembleLemmas` and are not
part of the public API of the campaign.

## Main definitions

* `TCSlib.Cryptography.EnsembleLemmas.coinsEquiv` — the coin-splitting bijection
  `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b` (`Fin.appendEquiv` transported along the
  length equation).
* `TCSlib.Cryptography.EnsembleLemmas.padL` — the padded/truncated string `padFin` as a list.
* `TCSlib.Cryptography.EnsembleLemmas.blocks` — the blockwise bijection
  `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (the copy of `Ensembles.lean`'s private `blocks`).
* `TCSlib.Cryptography.EnsembleLemmas.CopiesLoop` — the state loop sampling `t(n)` copies
  with the challenge planted at a hard-wired position (the multicopy reduction as an FP
  function).

## Main results

* `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv`, `acceptProb_coins_fst`,
  `acceptProb_not` — reindexing the coins of a distinguisher.
* `TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton` — no advantage on a
  one-point sample space.
* `TCSlib.Cryptography.EnsembleLemmas.exists_negRed`, `exists_pushRed`, `exists_copiesRed`
  — the machines of Lemmas 73.8, 71.5 and the multicopy corollary.
* `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam`, `acceptProb_reparam_advice`,
  `acceptProb_pushRed`, `acceptProb_negRed` — the acceptance probabilities of the
  reparametrised and composed machines.
* `TCSlib.Cryptography.EnsembleLemmas.statClose_copies`,
  `acceptProb_multicopyRed_congr` — replacing the ideal samplers of the multicopy reduction
  by exactly distributed polynomial-time samplers.
* `TCSlib.Cryptography.EnsembleLemmas.negligible_polyExpr_mul` — a syntactic polynomial
  times a negligible function is negligible.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.1.1: Lemmas 71.5, 71.6 and 73.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Lemmas 3.2 and 3.3).
-/

namespace TCSlib.Cryptography.EnsembleLemmas

open Complexity Turing Finset

/-! ### Reindexing acceptance probabilities -/

section Probability

variable {σ τ γ ρ κ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] [Fintype κ]

/-- Relabelling the coin space of a distinguisher by a bijection does not change the
acceptance probability (the coin analogue of `acceptProb_comp_equiv`). -/
theorem acceptProb_coins_equiv (e : κ ≃ ρ) (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z c => D z (e c)) = acceptProb X D :=
  uprob_eq_of_equiv ((Equiv.refl σ).prodCongr e)
    (q := fun w : σ × ρ => D (X w.1) w.2 = true) fun _ => Iff.rfl

/-- Coins the distinguisher never reads (a second, ignored coin factor) do not change the
acceptance probability. -/
theorem acceptProb_coins_fst [Nonempty κ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z (c : ρ × κ) => D z c.1) = acceptProb X D :=
  (uprob_eq_of_equiv (Equiv.prodAssoc σ ρ κ).symm
    (q := fun w : (σ × ρ) × κ => D (X w.1.1) w.1.2 = true) fun _ => Iff.rfl).trans
    (uprob_fst fun w : σ × ρ => D (X w.1) w.2 = true)

/-- Negating the verdict complements the acceptance probability. -/
theorem acceptProb_not [Nonempty σ] [Nonempty ρ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z c => !(D z c)) = 1 - acceptProb X D := by
  unfold acceptProb
  rw [← uprob_not]
  congr 1
  funext w
  simp

/-- The probability of a constant event on a nonempty type is its indicator. -/
theorem uprob_const {α : Type*} [Fintype α] [Nonempty α] (p : Prop) [Decidable p] :
    uprob (fun _ : α => p) = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]
    have : (fun _ : α => p) = fun _ => True :=
      funext fun _ => propext ⟨fun _ => trivial, fun _ => hp⟩
    rw [this, uprob_true]
  · rw [if_neg hp]
    have : (fun _ : α => p) = fun _ => False := funext fun _ => propext ⟨hp, False.elim⟩
    rw [this, uprob_false]

/-- Two samplers into a subsingleton type have the same law. -/
theorem statClose_of_subsingleton [Subsingleton γ] [Nonempty σ] [Nonempty τ] (X : σ → γ)
    (Y : τ → γ) : StatClose X Y 0 := by
  classical
  intro T
  have c := X (Classical.arbitrary σ)
  have hX : ∀ s, X s = c := fun s => Subsingleton.elim _ _
  have hY : ∀ t, Y t = c := fun t => Subsingleton.elim _ _
  simp only [hX, hY, uprob_const, sub_self, abs_zero, le_refl]

/-- No distinguisher has an advantage between two samplers into a subsingleton type (the
case `t(n) = 0` of the multicopy corollary). -/
theorem distAdv_eq_zero_of_subsingleton [Subsingleton γ] [Nonempty σ] [Nonempty τ] (X : σ → γ)
    (Y : τ → γ) (D : γ → ρ → Bool) : distAdv X Y D = 0 :=
  le_antisymm (distAdv_le_of_statClose X Y (statClose_of_subsingleton X Y) D) (abs_nonneg _)

end Probability

/-! ### Coin splitting -/

/-- The coin-splitting bijection `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b`:
`Fin.appendEquiv` transported along the length equation. -/
def coinsEquiv {m a b : ℕ} (h : m = a + b) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin m → Bool) :=
  (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The coin string of a split pair is the concatenation of the two coin strings. -/
theorem ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (coinsEquiv h c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [← List.ofFn_fin_append]
  exact (List.ofFn_congr h.symm (Fin.append c.1 c.2)).symm

/-- The first `a` coins of a split pair. -/
theorem take_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    (List.ofFn (coinsEquiv h c)).take a = List.ofFn c.1 := by
  rw [ofFn_coinsEquiv, List.take_left' List.length_ofFn]

/-- The coins of a split pair after the first `a`. -/
theorem drop_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    (List.ofFn (coinsEquiv h c)).drop a = List.ofFn c.2 := by
  rw [ofFn_coinsEquiv, List.drop_left' List.length_ofFn]

/-! ### Padding as an FP function -/

/-- The padded/truncated string of `padFin` as a list: exactly `k` bits, the bits of `a`
followed by `false`s. -/
def padL (k : ℕ) (a : List Bool) : List Bool := List.ofFn (padFin k a)

/-- `padL` has exactly `k` bits. -/
theorem length_padL (k : ℕ) (a : List Bool) : (padL k a).length = k := List.length_ofFn

/-- `padL k a` is the first `k` bits of `a ++ 0^k`. -/
theorem padL_eq (k : ℕ) (a : List Bool) : padL k a = (a ++ List.replicate k false).take k := by
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp [padL]
  · simp only [padL, List.getElem_ofFn, padFin, List.getD_eq_getElem?_getD, List.getElem_take,
      List.getElem_append]
    split_ifs with h
    · simp [List.getElem?_eq_getElem h]
    · simp [List.getElem?_eq_none_iff.2 (not_lt.1 h)]

/-- Composition of polynomial-time functions, in applied form. -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The all-`false` string `0^{p(|u z|)}` is polynomial-time: the bitwise xor of `1^{p(|u z|)}`
with itself (`Complexity.polyTimeComputable_pairXor`, `Complexity.polyTimeComputable_unaryPoly`). -/
theorem polyTimeComputable_zeros (p : PolyExpr) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) :
    PolyTimeComputable fun z => List.replicate (p.eval (u z).length) false := by
  have h1 := StateLoop.unaryPoly_comp p hu
  convert ptc_comp polyTimeComputable_pairXor (h1.pairEncode h1) using 1
  funext z
  simp

/-- **Padding is polynomial-time:** `z ↦ padL (p(|u z|)) (a z)` for polynomial-time `u`, `a`
(the first `p(|u z|)` bits of `a z ++ 0^{p(|u z|)}`, a typed cut
`Complexity.polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_padL (p : PolyExpr) {u a : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) :
    PolyTimeComputable fun z => padL (p.eval (u z).length) (a z) := by
  convert ptc_comp (polyTimeComputable_pairTakePoly p)
    (hu.pairEncode (ha.append (polyTimeComputable_zeros p hu))) using 1
  funext z
  simp [padL_eq]

/-! ### The negated distinguisher of the prediction lemma -/

/-- Negating a verdict (`[true] ↦ [false]`, anything else `↦ [true]`) is polynomial-time
(`Complexity.polyTimeComputable_ite` on the equality test `Complexity.polyTimeComputable_pairEq`). -/
theorem polyTimeComputable_negVerdict :
    PolyTimeComputable fun w => if w = [true] then [false] else [true] := by
  have htest : PolyTimeComputable fun w => [decide (w = [true])] := by
    convert ptc_comp polyTimeComputable_pairEq
      (polyTimeComputable_id.pairEncode (polyTimeComputable_const [true])) using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext w
  simp

/-- **The negated machine** of [PS10, Lemma 73.8]: for an `NUPPT` `D` there is an `NUPPT`
`B` with the same coins outputting `[true]` iff `D` does not output `[true]`
(`Complexity.NUPPT.exists_comp` with the post-processing `polyTimeComputable_negVerdict`). -/
theorem exists_negRed (D : NUPPT) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = if D.runAtL n y r = [true] then [false] else [true] := by
  obtain ⟨B, hc, -, -, hB⟩ := D.exists_comp polyTimeComputable_id polyTimeComputable_negVerdict
  exact ⟨B, hc, hB⟩

/-- The negated machine accepts exactly when the original rejects: its acceptance probability
is the complement. -/
theorem acceptProb_negRed {σ : Type*} [Fintype σ] [Nonempty σ] {B D : NUPPT} (hBc : B.coins = D.coins)
    (hB : ∀ n y r, B.runAtL n y r = if D.runAtL n y r = [true] then [false] else [true])
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) = 1 - acceptProb X (D.distinguisher n m) := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen, hBc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← acceptProb_coins_equiv e, ← acceptProb_not]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hofn, hB]
  split_ifs <;> simp_all

/-! ### Parameter changes -/

/-- The acceptance probability of `NUPPT.exists_reparam D p` at parameter `n` is that of `D`
at parameter `p(n)`: the coin types correspond along `PolyExpr.eval_subst`. -/
theorem acceptProb_reparam {σ : Type*} [Fintype σ] {B D : NUPPT} {p : PolyExpr}
    (hBc : B.coins = D.coins.subst p) (hB : ∀ n y r, B.runAtL n y r = D.runAtL (p.eval n) y r)
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) = acceptProb X (D.distinguisher (p.eval n) m) := by
  have hlen : D.coinLen (p.eval n) = B.coinLen n := by
    simp [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
  let e : D.Coins (p.eval n) ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hofn, hB]

/-- The acceptance probability of `NUPPT.exists_reparam_advice D φ p` at parameter `m` is that
of `D` at parameter `φ m`: the unread coins are an independent uniform factor
(`acceptProb_coins_fst`) after the split `coinsEquiv`. -/
theorem acceptProb_reparam_advice {σ : Type*} [Fintype σ] {A D : NUPPT} {φ : ℕ → ℕ} {p : PolyExpr}
    (hAc : A.coins = D.coins.subst p)
    (hA : ∀ n y r, A.runAtL n y r = D.runAtL (φ n) y (r.take (D.coinLen (φ n))))
    (m : ℕ) (hle : D.coinLen (φ m) ≤ D.coinLen (p.eval m)) (k : ℕ) (X : σ → Fin k → Bool) :
    acceptProb X (A.distinguisher m k) = acceptProb X (D.distinguisher (φ m) k) := by
  have hlen : A.coinLen m = D.coinLen (φ m) + (D.coinLen (p.eval m) - D.coinLen (φ m)) := by
    have : A.coinLen m = D.coinLen (p.eval m) := by
      simp [NUPPT.coinLen, hAc, PolyExpr.eval_subst]
    omega
  rw [← acceptProb_coins_equiv (coinsEquiv hlen)]
  conv_rhs => rw [← acceptProb_coins_fst (κ := Fin (D.coinLen (p.eval m) - D.coinLen (φ m)) → Bool)
    X (D.distinguisher (φ m) k)]
  congr 1
  funext z c
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hA, take_ofFn_coinsEquiv]

/-! ### The machine of Lemma 71.5 -/

/-- **The machine of [PS10, Lemma 71.5]:** for `NUPPT`s `M`, `D` and an output length `ℓ'`
there is an `NUPPT` `B` with coins `M.coins + D.coins` that runs `M` on its input with the
first `M.coins n` coins, pads the result to `ℓ'(n)` bits and hands it to `D` with the remaining
coins. The padding is done inside the raw function of the layout, where `1^n` is available
(run-3 audit note P2-4: `NUPPT.exists_comp` sees only `y`).

**Proof sketch.** As `Complexity.NUPPT.exists_seq`: advice `combineAdvice (M.advice n) (D.advice n)`;
the raw function cuts the coins at `M.coins(|1^n|)` (`polyTimeComputable_pairTakePoly`/`pairDropPoly`),
runs `M.output` on `layout (inParam z) (inArg z) (pairFstD (inAdvice z)) r₁`, pads with
`polyTimeComputable_padL ℓ'` against `inParam z`, and runs `D.output` on
`layout (inParam z) (padded) (pairSndD (inAdvice z)) r₂`; the equation is
`NUPPT.runAtL_ofPolyTime` plus the projection identities. -/
theorem exists_pushRed (M D : NUPPT) (ℓ' : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add M.coins D.coins ∧
      ∀ n y r, B.runAtL n y r =
        D.runAtL n (padL (ℓ'.eval n) (M.runAtL n y (r.take (M.coinLen n)))) (r.drop (M.coinLen n)) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hr₁ := ptc_comp (polyTimeComputable_pairTakePoly M.coins) hcut
  have hr₂ := ptc_comp (polyTimeComputable_pairDropPoly M.coins) hcut
  have ha := ptc_comp M.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      NUPPT.polyTimeComputable_inArg
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice) hr₁)
  have hpad := polyTimeComputable_padL ℓ' NUPPT.polyTimeComputable_inParam ha
  have hF := ptc_comp D.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hpad
      (ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice) hr₂)
  have hadv : ∀ n, (NUPPT.combineAdvice (M.advice n) (D.advice n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) M.adv) (.const 2)) D.adv).eval n := fun n => by
    have h₁ := NUPPT.length_combineAdvice_le (M.advice n) (D.advice n)
    have h₂ := M.advice_length n
    have h₃ := D.advice_length n
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  refine ⟨NUPPT.ofPolyTime hF (.add M.coins D.coins) _
    (fun n => NUPPT.combineAdvice (M.advice n) (D.advice n)) hadv, rfl, fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.advInput, NUPPT.coinLen, NUPPT.layout, NUPPT.inParam, NUPPT.inArg,
    NUPPT.inAdvice, NUPPT.inCoins]

/-- The acceptance probability of the machine of `exists_pushRed` on a sampler `X` is the
acceptance probability of `D` on the pushed sampler `(s, c) ↦ padFin (ℓ' n) (M(1^n, X s; c))`
(`acceptProb_bind` after the coin split `coinsEquiv`). -/
theorem acceptProb_pushRed {σ : Type*} [Fintype σ] {M D B : NUPPT} {ℓ' : PolyExpr}
    (hBc : B.coins = .add M.coins D.coins)
    (hB : ∀ n y r, B.runAtL n y r =
      D.runAtL n (padL (ℓ'.eval n) (M.runAtL n y (r.take (M.coinLen n)))) (r.drop (M.coinLen n)))
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) =
      acceptProb (fun z : σ × M.Coins n => padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X z.1)) z.2))
        (D.distinguisher n (ℓ'.eval n)) := by
  have hlen : B.coinLen n = M.coinLen n + D.coinLen n := by simp [NUPPT.coinLen, hBc]
  rw [← acceptProb_coins_equiv (coinsEquiv hlen),
    ← acceptProb_bind X (fun t c => padFin (ℓ'.eval n) (M.runAt n (List.ofFn t) c))
      (D.distinguisher n (ℓ'.eval n))]
  congr 1
  funext z c
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hB, take_ofFn_coinsEquiv, drop_ofFn_coinsEquiv,
    padL]

/-! ### Negligible functions and syntactic polynomials -/

/-- A syntactic polynomial times a negligible function is negligible: `p(n) ≤ C(n+1)^c ≤
C 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), then `Negligible.mul_pow` and
`Negligible.const_mul`. -/
theorem negligible_polyExpr_mul (p : PolyExpr) {μ : ℕ → ℝ} (hμ : Negligible μ) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  refine ((hμ.mul_pow e).const_mul ((C * 2 ^ e : ℕ) : ℝ)).mono ⟨1, fun n hn => ?_⟩
  have hp : (0 : ℝ) ≤ p.eval n := by positivity
  have hC : (0 : ℝ) ≤ ((C * 2 ^ e : ℕ) : ℝ) := by positivity
  have hne : (0 : ℝ) ≤ (n : ℝ) ^ e := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hC, abs_of_nonneg hne]
  have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
  have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
    apply pow_le_pow_left₀ (by positivity)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc (p.eval n : ℝ) * |μ n| ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * |μ n| :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
          (abs_nonneg _)
    _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * |μ n|) := by push_cast; ring

/-! ### Blocks and chunks -/

/-- The blockwise bijection `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (the copy of the private `blocks` of
`Asymptotic/Ensembles.lean` and `Asymptotic/OneWay.lean`): block `i`, bit `j` is bit
`finProdFinEquiv (i, j) = j + ℓ·i` of the string. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- Unfolding `blocks`. -/
theorem blocks_apply (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    blocks q ℓ w i j = w (finProdFinEquiv (i, j)) := rfl

/-- Unfolding `blocks.symm`. -/
theorem blocks_symm_apply (q ℓ : ℕ) (V : Fin q → Fin ℓ → Bool) (x : Fin (q * ℓ)) :
    (blocks q ℓ).symm V x = V (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := rfl

/-- The index `i·ℓ + j` decodes to block `i`, bit `j`. -/
theorem finProdFinEquiv_symm_mk {q ℓ : ℕ} (i : Fin q) (j : Fin ℓ) (h : i * ℓ + j < q * ℓ) :
    finProdFinEquiv.symm (⟨i * ℓ + j, h⟩ : Fin (q * ℓ)) = (i, j) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [finProdFinEquiv]
  ring

/-- The `i`-th chunk of `s` bits of the string of a `q·s`-bit word is its block `i`. -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (blocks q s w ⟨i, hi⟩) := by
  have hle : i * s + s ≤ q * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s hi
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, blocks_apply]
    congr 1
    ext
    simp [finProdFinEquiv]
    ring

/-- The string of `(blocks q ℓ).symm V` is the concatenation of the `q` block strings
(`List.ofFn_mul`). -/
theorem ofFn_blocks_symm {q ℓ : ℕ} (V : Fin q → Fin ℓ → Bool) (F : ℕ → List Bool)
    (hF : ∀ i (h : i < q), F i = List.ofFn (V ⟨i, h⟩)) :
    List.ofFn ((blocks q ℓ).symm V) = (List.range q).flatMap F := by
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange, List.map_map, List.ofFn_eq_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, hF i i.isLt]
  congr 1
  funext j
  rw [blocks_symm_apply, finProdFinEquiv_symm_mk]

/-- The concatenation of `q` chunks of `ℓ` bits has `q·ℓ` bits. -/
theorem length_flatMap_range (F : ℕ → List Bool) {q ℓ : ℕ} (hF : ∀ i < q, (F i).length = ℓ) :
    ((List.range q).flatMap F).length = q * ℓ := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append,
      ih fun i hi => hF i (Nat.lt_succ_of_lt hi), List.flatMap_singleton,
      hF q (Nat.lt_succ_self q), Nat.succ_mul]

/-- Truncating the concatenation of `m ≥ q` chunks to `q·ℓ` bits keeps the first `q` chunks. -/
theorem take_flatMap_range (F : ℕ → List Bool) {q m ℓ : ℕ} (hq : q ≤ m)
    (hF : ∀ i < q, (F i).length = ℓ) :
    ((List.range m).flatMap F).take (q * ℓ) = (List.range q).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [List.range_add, List.flatMap_append, List.take_left' (length_flatMap_range F hF)]

/-! ### Exactly distributed samplers under `copies` -/

/-- Splitting a tuple into its head and its tail. -/
def consSplit (κ : Type*) (t : ℕ) : (Fin (t + 1) → κ) ≃ κ × (Fin t → κ) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    ext <;> simp [Fin.tail_cons]

/-- Exactly distributed samplers stay exactly distributed under `copies`.

**Proof sketch.** Induction on the number of copies `t`. For `t = 0` both samplers take
values in the one-point type `Fin 0 → γ` (`statClose_of_subsingleton`). For `t + 1`,
`StatClose.prod` of the hypothesis with the induction hypothesis gives the pair sampler
`c ↦ (X' (c 0), copies t X' (tail c))`, `StatClose.map` with `Fin.cons` reassembles the
tuple, and `consSplit` reindexes both seed spaces along `(Fin (t+1) → κ) ≃ κ × (Fin t → κ)`;
the composite is `copies (t + 1)` by `Fin.cases`. -/
theorem statClose_copies {κ σ γ : Type*} [Fintype κ] [Fintype σ] {X' : κ → γ} {X : σ → γ}
    (h : StatClose X' X 0) : ∀ t : ℕ, StatClose (copies t X') (copies t X) 0
  | 0 => statClose_of_subsingleton _ _
  | t + 1 => by
    have hp := (h.prod (statClose_copies h t)).map
      fun p : γ × (Fin t → γ) => (Fin.cons p.1 p.2 : Fin (t + 1) → γ)
    rw [add_zero] at hp
    have e := (hp.comp_equiv_left (consSplit κ t)).comp_equiv_right (consSplit σ t)
    have h1 : copies (t + 1) X' =
        fun f => Fin.cons (X' ((consSplit κ t) f).1) (copies t X' ((consSplit κ t) f).2) := by
      funext f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [copies, consSplit]
      · simp [copies, consSplit, Fin.tail]
    have h2 : copies (t + 1) X =
        fun f => Fin.cons (X ((consSplit σ t) f).1) (copies t X ((consSplit σ t) f).2) := by
      funext f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [copies, consSplit]
      · simp [copies, consSplit, Fin.tail]
    rw [h1, h2]
    exact e

/-- Reindexing `ζ × (S × ρ) ≃ S × (ζ × ρ)`. -/
def swapAux (ζ S ρ : Type*) : ζ × (S × ρ) ≃ S × (ζ × ρ) where
  toFun w := (w.2.1, (w.1, w.2.2))
  invFun v := (v.2.1, (v.1, v.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Replacing the ideal samplers of the multicopy reduction by exactly distributed ones**
leaves the acceptance probability unchanged: the other `t − 1` copies are drawn from
`X'`, `Y'` (statistically identical to `X`, `Y`), the challenge `Z` and the coins of `D` are
auxiliary coins (`StatClose.abs_uprob_sub_le_prod` at `δ = 0` after `statClose_copies` and
`StatClose.prod`). -/
theorem acceptProb_multicopyRed_congr {κX κY σ τ ζ γ ρ : Type*} [Fintype κX] [Fintype κY]
    [Fintype σ] [Fintype τ] [Fintype ζ] [Fintype ρ] {X' : κX → γ} {X : σ → γ} {Y' : κY → γ}
    {Y : τ → γ} (hX : StatClose X' X 0) (hY : StatClose Y' Y 0) (Z : ζ → γ) (t k : ℕ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb Z (multicopyRed X' Y' t k D) = acceptProb Z (multicopyRed X Y t k D) := by
  have hG := (statClose_copies hX t).prod (statClose_copies hY t)
  rw [add_zero] at hG
  have key := hG.abs_uprob_sub_le_prod fun (uv : (Fin t → γ) × (Fin t → γ)) (w : ζ × ρ) =>
    D (fun i => if (i : ℕ) < k then uv.2 i else if (i : ℕ) = k then Z w.1 else uv.1 i) w.2 = true
  rw [abs_nonpos_iff, sub_eq_zero] at key
  calc acceptProb Z (multicopyRed X' Y' t k D)
      = uprob fun v : ((Fin t → κX) × (Fin t → κY)) × (ζ × ρ) =>
          D (fun i => if (i : ℕ) < k then copies t Y' v.1.2 i
            else if (i : ℕ) = k then Z v.2.1 else copies t X' v.1.1 i) v.2.2 = true :=
        uprob_eq_of_equiv (swapAux ζ ((Fin t → κX) × (Fin t → κY)) ρ) fun _ => Iff.rfl
    _ = uprob fun v : ((Fin t → σ) × (Fin t → τ)) × (ζ × ρ) =>
          D (fun i => if (i : ℕ) < k then copies t Y v.1.2 i
            else if (i : ℕ) = k then Z v.2.1 else copies t X v.1.1 i) v.2.2 = true := key
    _ = acceptProb Z (multicopyRed X Y t k D) :=
        (uprob_eq_of_equiv (swapAux ζ ((Fin t → σ) × (Fin t → τ)) ρ) fun _ => Iff.rfl).symm

/-! ### The sampler loop of the multicopy reduction -/

namespace CopiesLoop

/-- The parameter slot `u` of the state word `⟨u, ⟨cnt, ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The unary round counter `cnt` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The unary hybrid index `kk` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- The challenge `z` of the state word. -/
def p₄ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD w)))

/-- The remaining coins `rX` for the copies of `X`. -/
def p₅ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The remaining coins `rY` for the copies of `Y`. -/
def p₆ (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The state word `⟨u, ⟨cnt, ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`. -/
def st (u cnt kk z rX rY : List Bool) : List Bool :=
  pairEncode u (pairEncode cnt (pairEncode kk (pairEncode z (pairEncode rX rY))))

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u cnt kk z rX rY : List Bool) : p₁ (st u cnt kk z rX rY) = u := by
  simp [p₁, st]

/-- Reading the counter. -/
@[simp] theorem p₂_st (u cnt kk z rX rY : List Bool) : p₂ (st u cnt kk z rX rY) = cnt := by
  simp [p₂, st]

/-- Reading the hybrid index. -/
@[simp] theorem p₃_st (u cnt kk z rX rY : List Bool) : p₃ (st u cnt kk z rX rY) = kk := by
  simp [p₃, st]

/-- Reading the challenge. -/
@[simp] theorem p₄_st (u cnt kk z rX rY : List Bool) : p₄ (st u cnt kk z rX rY) = z := by
  simp [p₄, st]

/-- Reading the coins for `X`. -/
@[simp] theorem p₅_st (u cnt kk z rX rY : List Bool) : p₅ (st u cnt kk z rX rY) = rX := by
  simp [p₅, st]

/-- Reading the coins for `Y`. -/
@[simp] theorem p₆_st (u cnt kk z rX rY : List Bool) : p₆ (st u cnt kk z rX rY) = rY := by
  simp [p₆, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The projections are polynomial-time. -/
theorem p₄_poly : PolyTimeComputable p₄ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The projections are polynomial-time. -/
theorem p₅_poly : PolyTimeComputable p₅ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- The projections are polynomial-time. -/
theorem p₆_poly : PolyTimeComputable p₆ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- Assembling a state word from six polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ f₄ f₅ f₆ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) (h₄ : PolyTimeComputable f₄)
    (h₅ : PolyTimeComputable f₅) (h₆ : PolyTimeComputable f₆) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) (f₄ z) (f₅ z) (f₆ z) :=
  h₁.pairEncode (h₂.pairEncode (h₃.pairEncode (h₄.pairEncode (h₅.pairEncode h₆))))

/-- `2|fst z| + |snd z| ≤ |z|` for every word (equality plus two on pairs, `0 ≤ |z|` on
malformed words). -/
theorem two_mul_length_pairFstD_add_le (z : List Bool) :
    2 * (pairFstD z).length + (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, pairSndD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z a b h
    subst hz
    rw [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    omega

variable (sX sY : PolyExpr)

/-- The step: append a token to the counter and drop one chunk from each coin string
(`sX(|u|)` bits of `rX`, `sY(|u|)` bits of `rY`). -/
def step (w : List Bool) : List Bool :=
  st (p₁ w) (true :: p₂ w) (p₃ w) (p₄ w) ((p₅ w).drop (sX.eval (p₁ w).length))
    ((p₆ w).drop (sY.eval (p₁ w).length))

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rX⟩`,
`⟨u, rY⟩`). -/
theorem step_poly : PolyTimeComputable (step sX sY) := by
  convert st_poly p₁_poly (ptc_comp (StateLoop.cons_poly true) p₂_poly) p₃_poly p₄_poly
    (ptc_comp (polyTimeComputable_pairDropPoly sX) (p₁_poly.pairEncode p₅_poly))
    (ptc_comp (polyTimeComputable_pairDropPoly sY) (p₁_poly.pairEncode p₆_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most `12` symbols (the pairing overhead; the coins only
shrink). -/
theorem length_step_le (w : List Bool) : (step sX sY w).length ≤ w.length + 12 := by
  have h₁ := two_mul_length_pairFstD_add_le w
  have h₂ := two_mul_length_pairFstD_add_le (pairSndD w)
  have h₃ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD w))
  have h₄ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD (pairSndD w)))
  have h₅ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD (pairSndD (pairSndD w))))
  have d₅ : ((p₅ w).drop (sX.eval (p₁ w).length)).length ≤ (p₅ w).length := by simp
  have d₆ : ((p₆ w).drop (sY.eval (p₁ w).length)).length ≤ (p₆ w).length := by simp
  simp only [step, st, length_pairEncode, List.length_cons, p₁, p₂, p₃, p₄, p₅, p₆] at *
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    ((step sX sY)^[i] w).length ≤ w.length + 12 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le sX sY ((step sX sY)^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨[], ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`: after `i` rounds the
counter is `1^i` and `i` chunks have been dropped from each coin string. -/
theorem iterate_step (u kk z rX rY : List Bool) (i : ℕ) :
    (step sX sY)^[i] (st u [] kk z rX rY) =
      st u (List.replicate i true) kk z (rX.drop (i * sX.eval u.length))
        (rY.drop (i * sY.eval u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [step, List.replicate_succ, List.drop_drop, Nat.succ_mul]

variable (SX SY : List Bool → List Bool) (ℓ : PolyExpr)

/-- The emission at a state word: a padded sample of `Y` from the next `sY(|u|)` coins while
the counter is below the hybrid index, the challenge `z` at the hybrid index, and a padded
sample of `X` from the next `sX(|u|)` coins afterwards. -/
def emit (w : List Bool) : List Bool :=
  if (p₂ w).length < (p₃ w).length then
    padL (ℓ.eval (p₁ w).length) (SY (pairEncode (p₁ w) ((p₆ w).take (sY.eval (p₁ w).length))))
  else if (p₂ w).length = (p₃ w).length then p₄ w
  else padL (ℓ.eval (p₁ w).length) (SX (pairEncode (p₁ w) ((p₅ w).take (sX.eval (p₁ w).length))))

/-- The emission is polynomial-time: two length tests (`StateLoop.lenLe_comp`,
`Complexity.polyTimeComputable_lenEq`), two padded sampler calls (`polyTimeComputable_padL`,
`Complexity.polyTimeComputable_pairTakePoly`) and `Complexity.polyTimeComputable_ite`. -/
theorem emit_poly (hSX : PolyTimeComputable SX) (hSY : PolyTimeComputable SY) :
    PolyTimeComputable (emit sX sY SX SY ℓ) := by
  have hlt : PolyTimeComputable fun w => [decide ((p₂ w).length < (p₃ w).length)] := by
    exact StateLoop.lenLe_comp p₃_poly (ptc_comp (StateLoop.cons_poly true) p₂_poly)
  have heq : PolyTimeComputable fun w => [decide ((p₂ w).length = (p₃ w).length)] := by
    convert ptc_comp polyTimeComputable_lenEq (p₂_poly.pairEncode p₃_poly) using 1
    funext w
    simp
  have hY := polyTimeComputable_padL ℓ p₁_poly (ptc_comp hSY (p₁_poly.pairEncode
    (ptc_comp (polyTimeComputable_pairTakePoly sY) (p₁_poly.pairEncode p₆_poly))))
  have hX := polyTimeComputable_padL ℓ p₁_poly (ptc_comp hSX (p₁_poly.pairEncode
    (ptc_comp (polyTimeComputable_pairTakePoly sX) (p₁_poly.pairEncode p₅_poly))))
  convert polyTimeComputable_ite hlt hY (polyTimeComputable_ite heq p₄_poly hX) using 1
  funext w
  simp [emit]

/-- The emission at a genuine state word with unary parameter, counter and index. -/
theorem emit_st (n cnt k : ℕ) (z rX rY : List Bool) :
    emit sX sY SX SY ℓ
        (st (List.replicate n true) (List.replicate cnt true) (List.replicate k true) z rX rY) =
      if cnt < k then
        padL (ℓ.eval n) (SY (pairEncode (List.replicate n true) (rY.take (sY.eval n))))
      else if cnt = k then z
      else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true) (rX.take (sX.eval n)))) := by
  simp [emit]

variable (t : PolyExpr)

/-- The loop output: the `t(|x|) + 1` emissions along the orbit of `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (t.eval x.length + 1)).flatMap fun i => emit sX sY SX SY ℓ ((step sX sY)^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 12 t(|x|)`). -/
theorem loopOut_poly (hSX : PolyTimeComputable SX) (hSY : PolyTimeComputable SY) :
    PolyTimeComputable (loopOut sX sY SX SY ℓ t) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit (step_poly sX sY) (emit_poly sX sY SX SY ℓ hSX hSY) t
    (.add .var (.mul (.const 12) t)) fun x i hi => ?_
  have h := length_iterate_step_le sX sY x i
  have h' : 12 * i ≤ 12 * t.eval x.length := Nat.mul_le_mul_left 12 hi
  simp only [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-- The loop output on the genuine initial state: chunk `i` is a padded sample of `Y` from
the `i`-th chunk of `rY` below the index `k`, the challenge at `k`, and a padded sample of `X`
from the `i`-th chunk of `rX` above `k`. -/
theorem loopOut_st (n k : ℕ) (z rX rY : List Bool) :
    loopOut sX sY SX SY ℓ t (st (List.replicate n true) [] (List.replicate k true) z rX rY) =
      (List.range (t.eval (st (List.replicate n true) [] (List.replicate k true) z rX rY).length
        + 1)).flatMap fun i =>
          if i < k then
            padL (ℓ.eval n) (SY (pairEncode (List.replicate n true)
              ((rY.drop (i * sY.eval n)).take (sY.eval n))))
          else if i = k then z
          else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true)
            ((rX.drop (i * sX.eval n)).take (sX.eval n)))) := by
  unfold loopOut
  congr 1
  funext i
  rw [iterate_step, emit_st]
  simp

end CopiesLoop

/-- The initial state of the sampler loop as a function of the raw layout
`⟨⟨⟨1^n, ⟨z, 1^k⟩⟩, α⟩, r⟩`: `⟨1^n, ⟨[], ⟨1^k, ⟨z, ⟨r.take (t·sX)(n), r.drop (t·sX)(n)⟩⟩⟩⟩⟩`. -/
def copiesInit (sX t : PolyExpr) (w : List Bool) : List Bool :=
  CopiesLoop.st (NUPPT.inParam w) [] (pairSndD (NUPPT.inArg w)) (pairFstD (NUPPT.inArg w))
    ((NUPPT.inCoins w).take ((PolyExpr.mul t sX).eval (NUPPT.inParam w).length))
    ((NUPPT.inCoins w).drop ((PolyExpr.mul t sX).eval (NUPPT.inParam w).length))

/-- The initial state is polynomial-time in the raw layout. -/
theorem copiesInit_poly (sX t : PolyExpr) : PolyTimeComputable (copiesInit sX t) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  convert CopiesLoop.st_poly NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
    (ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
    (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg)
    (ptc_comp (polyTimeComputable_pairTakePoly (.mul t sX)) hcut)
    (ptc_comp (polyTimeComputable_pairDropPoly (.mul t sX)) hcut) using 1
  funext w
  simp [copiesInit]

/-- The raw function of the sampler machine: the loop output on the initial state, truncated
to `t(n)·ℓ(n)` bits. -/
def copiesSampler (SX SY : List Bool → List Bool) (sX sY ℓ t : PolyExpr) (w : List Bool) :
    List Bool :=
  (CopiesLoop.loopOut sX sY SX SY ℓ t (copiesInit sX t w)).take
    ((PolyExpr.mul t ℓ).eval (NUPPT.inParam w).length)

/-- The sampler function is polynomial-time. -/
theorem copiesSampler_poly {SX SY : List Bool → List Bool} (hSX : PolyTimeComputable SX)
    (hSY : PolyTimeComputable SY) (sX sY ℓ t : PolyExpr) :
    PolyTimeComputable (copiesSampler SX SY sX sY ℓ t) := by
  convert ptc_comp (polyTimeComputable_pairTakePoly (.mul t ℓ))
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (ptc_comp (CopiesLoop.loopOut_poly sX sY SX SY ℓ t hSX hSY) (copiesInit_poly sX t))) using 1
  funext w
  simp [copiesSampler]

/-- **The machine of the multicopy corollary** [PS10, Lemma 71.6; Gar26, Lemma 3.3]: for an
`NUPPT` `D`, polynomial-time samplers `SX`, `SY` with seed lengths `sX`, `sY`, a sample length
`ℓ`, a number of copies `t` and a hybrid index `k n ≤ t n`, there is an `NUPPT` `B` with coins
`t·sX + t·sY + D.coins` that on the challenge `z` and the coins `⟨cX, cY⟩ ++ cD` (the coins of
the samplers in blocks, then the coins of `D`) runs `D` on the tuple with the `i`-th position
holding a padded sample of `Y` from `cY i` for `i < k n`, the challenge at `i = k n`, and a
padded sample of `X` from `cX i` for `i > k n`.

**Proof sketch.** The uniform sampler machine `M₀ := ofPolyTimeUniform copiesSampler_poly`
runs the state loop `CopiesLoop` on `⟨1^n, ⟨[], ⟨1^k, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩` for `t(|x|) + 1 ≥ t(n)`
rounds and truncates to `t(n)·ℓ(n)` bits (`take_flatMap_range`); the `i`-th chunk is the
`i`-th block of the coins (`take_drop_ofFn_blocks`) and the concatenation of the blocks is the
string of `(blocks t ℓ).symm` (`ofFn_blocks_symm`). The reduction is
`NUPPT.exists_withAdvice (NUPPT.exists_seq M₀ (NUPPT.exists_comp D pairSndD id)) (1^{k n})`,
which hard-wires the hybrid index and hands the tuple to `D` with the remaining coins. -/
theorem exists_copiesRed (D : NUPPT) {SX SY : List Bool → List Bool} (hSX : PolyTimeComputable SX)
    (hSY : PolyTimeComputable SY) (sX sY ℓ t : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ t.eval n) :
    ∃ B : NUPPT, B.coins = .add (.add (.mul t sX) (.mul t sY)) D.coins ∧
      ∀ n (z : Fin (ℓ.eval n) → Bool) (cX : Fin (t.eval n) → Fin (sX.eval n) → Bool)
        (cY : Fin (t.eval n) → Fin (sY.eval n) → Bool) (cD : List Bool),
        B.runAtL n (List.ofFn z)
          (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
            List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY) ++ cD) =
        D.runAtL n (List.ofFn ((blocks (t.eval n) (ℓ.eval n)).symm fun i =>
          if (i : ℕ) < k n then padFin (ℓ.eval n) (SY (NUPPT.advInput n (List.ofFn (cY i))))
          else if (i : ℕ) = k n then z
          else padFin (ℓ.eval n) (SX (NUPPT.advInput n (List.ofFn (cX i)))))) cD := by
  obtain ⟨D₂, hD₂c, -, -, hD₂⟩ := D.exists_comp polyTimeComputable_pairSndD polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ := NUPPT.exists_seq
    (NUPPT.ofPolyTimeUniform (copiesSampler_poly hSX hSY sX sY ℓ t) (.add (.mul t sX) (.mul t sY)))
    D₂
  obtain ⟨B, hBc, hB⟩ := C.exists_withAdvice (fun n => List.replicate (k n) true) t
    (fun n => by simpa using hk n)
  refine ⟨B, by rw [hBc, hCc, hD₂c]; rfl, fun n z cX cY cD => ?_⟩
  rw [hB, hC, hD₂]
  have hlen : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).length =
      (NUPPT.ofPolyTimeUniform (copiesSampler_poly hSX hSY sX sY ℓ t)
        (.add (.mul t sX) (.mul t sY))).coinLen n := by
    simp [NUPPT.coinLen]
  rw [List.take_left' hlen, List.drop_left' hlen, id, pairSndD_pairEncode]
  congr 1
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  -- the sampler function on the layout
  have hX' : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).take
        ((PolyExpr.mul t sX).eval (List.replicate n true).length) =
      List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) := by
    rw [List.take_left']
    simp
  have hY' : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).drop
        ((PolyExpr.mul t sX).eval (List.replicate n true).length) =
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY) := by
    rw [List.drop_left']
    simp
  simp only [copiesSampler, copiesInit, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput,
    pairFstD_pairEncode, pairSndD_pairEncode, hX', hY']
  rw [CopiesLoop.loopOut_st]
  set F : ℕ → List Bool := fun i =>
    if i < k n then
      padL (ℓ.eval n) (SY (pairEncode (List.replicate n true)
        (((List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).drop (i * sY.eval n)).take
          (sY.eval n))))
    else if i = k n then List.ofFn z
    else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true)
      (((List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX)).drop (i * sX.eval n)).take
        (sX.eval n)))) with hF
  have hFlen : ∀ i < t.eval n, (F i).length = ℓ.eval n := by
    intro i _
    simp only [hF]
    split_ifs <;> simp [length_padL]
  have hq : t.eval n ≤ t.eval (CopiesLoop.st (List.replicate n true) [] (List.replicate (k n) true)
      (List.ofFn z) (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX))
      (List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY))).length + 1 := by
    refine (t.eval_mono ?_).trans (Nat.le_succ _)
    simp only [CopiesLoop.st, length_pairEncode, List.length_replicate]
    omega
  rw [PolyExpr.eval_mul, List.length_replicate, take_flatMap_range F hq hFlen]
  refine (ofFn_blocks_symm _ F fun i hi => ?_).symm
  simp only [hF]
  split_ifs with h₁ h₂
  · simp only [padL, take_drop_ofFn_blocks _ i hi, Equiv.apply_symm_apply]
  · rfl
  · simp only [padL, take_drop_ofFn_blocks _ i hi, Equiv.apply_symm_apply]

end TCSlib.Cryptography.EnsembleLemmas
