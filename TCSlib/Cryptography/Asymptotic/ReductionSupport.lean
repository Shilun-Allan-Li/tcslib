/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.Pseudorandom.Generators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shared support for polynomial-time reductions

The one-call wrapper and the parameter-aware pre-processor expose their typed
coin conversions and run equations. The bit-string identities, uniform coin
reindexing, polynomial-time cuts, and negligible bounds support multiple reductions.

## Main definitions

* `Complexity.NUPPT.wrap` is a one-call reduction with pre- and post-processing.
* `Complexity.NUPPT.preComp` lets pre-processing inspect the security parameter.
* `TCSlib.Cryptography.finCastEquiv` transports bit strings along a length equality.

## Main results

* `Complexity.NUPPT.runAt_wrap` and `Complexity.NUPPT.runAt_preComp` give the
  typed run equations.
* `TCSlib.Cryptography.prgAdv_coins_equiv` reindexes uniform coins.
* `TCSlib.Cryptography.Negligible.polyExpr_mul` bounds multiplication by a
  syntactic polynomial.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4, §3.3.5, §3.4.2, and §3.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §1.2 and Chapter 3.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Bit-string identities -/

/-- `List.ofFn (Fin.snoc v b) = List.ofFn v ++ [b]`. -/
theorem ofFn_snoc_eq {n : ℕ} (v : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc v b : Fin (n + 1) → Bool) = List.ofFn v ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- `List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last n)]`. -/
theorem ofFn_eq_init_append {n : ℕ} (v : Fin (n + 1) → Bool) :
    List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last n)] := by
  have h := ofFn_snoc_eq (Fin.init v) (v (Fin.last n))
  rwa [Fin.snoc_init_self] at h

/-- `List.ofFn` of an appended pair is the concatenation of the encodings. -/
theorem ofFn_appendEquiv {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    List.ofFn (Fin.appendEquiv a b (x, y)) = List.ofFn x ++ List.ofFn y :=
  List.ofFn_fin_append x y

/-- The first `a` bits of `List.ofFn x ++ List.ofFn y` with `|x| = a`. -/
theorem take_ofFn_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (List.ofFn x ++ List.ofFn y).take a = List.ofFn x :=
  List.take_left' (List.length_ofFn)

/-- The bits after the first `a` of `List.ofFn x ++ List.ofFn y` with `|x| = a`. -/
theorem drop_ofFn_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (List.ofFn x ++ List.ofFn y).drop a = List.ofFn y :=
  List.drop_left' (List.length_ofFn)

/-- Transport of bit strings along an equality of lengths (`Fin.cast` on the index). -/
def finCastEquiv {a b : ℕ} (h : a = b) : (Fin a → Bool) ≃ (Fin b → Bool) where
  toFun f j := f (Fin.cast h.symm j)
  invFun f i := f (Fin.cast h i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forward reader of `finCastEquiv`: bit `j` of the transported string is bit
`Fin.cast h.symm j` of `f`. -/
theorem finCastEquiv_apply {a b : ℕ} (h : a = b) (f : Fin a → Bool) (j : Fin b) :
    finCastEquiv h f j = f (Fin.cast h.symm j) :=
  rfl

/-- The function of `finCastEquiv h`: `f ↦ (j ↦ f (Fin.cast h.symm j))`. -/
theorem coe_finCastEquiv {a b : ℕ} (h : a = b) :
    ⇑(finCastEquiv h) = fun f j => f (Fin.cast h.symm j) :=
  rfl

/-- Transport along an equality of lengths does not change the encoding. -/
theorem ofFn_finCastEquiv {a b : ℕ} (h : a = b) (f : Fin a → Bool) :
    List.ofFn (finCastEquiv h f) = List.ofFn f :=
  (List.ofFn_congr h f).symm

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## The one-call wrapper -/

/-- The raw function of the one-call wrapper on the layout `⟨⟨⟨1^n, y⟩, ⟨β, α⟩⟩, r⟩`: cut the
coins at `p(n)`, form the view `w := ⟨⟨⟨1^n, y⟩, r.take (p n)⟩, β⟩`, run `A` on `pre w` with
advice `α` and the remaining coins, and return `post ⟨w, answer⟩`. -/
def wrapFun (A : NUPPT) (pre post : List Bool → List Bool) (p : PolyExpr) (z : List Bool) :
    List Bool :=
  post (pairEncode
    (layout (inParam z) (inArg z)
      ((pairSndD (pairEncode (inParam z) (inCoins z))).take
        (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length))
      (pairFstD (inAdvice z)))
    (A.output (layout (inParam z)
      (pre (layout (inParam z) (inArg z)
        ((pairSndD (pairEncode (inParam z) (inCoins z))).take
          (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length))
        (pairFstD (inAdvice z))))
      (pairSndD (inAdvice z))
      ((pairSndD (pairEncode (inParam z) (inCoins z))).drop
        (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length)))))

/-- The raw function of the one-call wrapper is polynomial-time (the pairing calculus, the
typed coin cuts `polyTimeComputable_pairTakePoly`/`pairDropPoly`, and `A.output`). -/
theorem wrapFun_poly (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (p : PolyExpr) :
    PolyTimeComputable (A.wrapFun pre post p) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have htake := (polyTimeComputable_pairTakePoly p).comp hcut
  have hdrop := (polyTimeComputable_pairDropPoly p).comp hcut
  have hw := polyTimeComputable_layout polyTimeComputable_inParam polyTimeComputable_inArg htake
    (polyTimeComputable_pairFstD.comp polyTimeComputable_inAdvice)
  have hA := A.polyTimeComputable_output.comp
    (polyTimeComputable_layout polyTimeComputable_inParam (hpre.comp hw)
      (polyTimeComputable_pairSndD.comp polyTimeComputable_inAdvice) hdrop)
  exact hpost.comp (hw.pairEncode hA)

/-- **The one-call wrapper** [PS10, §2.1, the closure properties used implicitly]: the
machine with coins `p + A.coins` and advice `⟨β n, A.advice n⟩` that, on `⟨1^n, y⟩` with coins
`r`, forms the view `w = ⟨⟨⟨1^n, y⟩, r.take (p n)⟩, β n⟩`, calls `A(1^n, pre w)` once with the
remaining coins and returns `post ⟨w, answer⟩`. Every single-call reduction of the hard-core
chapter is an instance (`runAtL_wrap`, `runAt_wrap`). -/
noncomputable def wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) : NUPPT :=
  ofPolyTime (A.wrapFun_poly hpre hpost p) (.add p A.coins)
    (.add (.add (.mul (.const 2) b) (.const 2)) A.adv)
    (fun n => pairEncode (β n) (A.advice n)) (fun n => by
      rw [length_pairEncode]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have h₁ := hβ n
      have h₂ := A.advice_length n
      omega)

/-- The coin polynomial of the one-call wrapper is `p + A.coins`. -/
@[simp] theorem coins_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) :
    (A.wrap hpre hpost β b hβ p).coins = .add p A.coins :=
  NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **The coins of the one-call wrapper**: the published equivalence `(A.wrap …).Coins n ≃
{0,1}^{p(n) + |A's coins at n|}` (data coins, then `A`'s coins; `finCongr` along the coin count). -/
noncomputable def wrapCoinsEquiv (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) :
    (A.wrap hpre hpost β b hβ p).Coins n ≃ (Fin (p.eval n + A.coinLen n) → Bool) :=
  Equiv.arrowCongr (finCongr
    (by rw [coinLen_eq, coins_wrap, PolyExpr.eval_add, coinLen_eq])) (Equiv.refl Bool)

/-- The inverse coin equivalence of the wrapper keeps the coin string:
`List.ofFn ((wrapCoinsEquiv … n).symm w) = List.ofFn w`. -/
theorem wrapCoinsEquiv_symm_ofFn (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ)
    (w : Fin (p.eval n + A.coinLen n) → Bool) :
    List.ofFn ((A.wrapCoinsEquiv hpre hpost β b hβ p n).symm w) = List.ofFn w :=
  List.ofFn_congr (by rw [coinLen_eq, coins_wrap, PolyExpr.eval_add, coinLen_eq]) _

/-- The untyped activation of the one-call wrapper. -/
theorem runAtL_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (y r : List Bool) :
    (A.wrap hpre hpost β b hβ p).runAtL n y r =
      post (pairEncode (layout (List.replicate n true) y (r.take (p.eval n)) (β n))
        (A.runAtL n (pre (layout (List.replicate n true) y (r.take (p.eval n)) (β n)))
          (r.drop (p.eval n)))) := by
  unfold wrap
  rw [runAtL_ofPolyTime]
  simp [wrapFun, runAtL_eq, advInput_eq, layout_eq, inParam_eq, inArg_eq, inAdvice_eq, inCoins_eq]

/-- The typed activation of the one-call wrapper on coins `r` that split as `a ++ c`: the
data coins `a` (`p(n)` bits) and the coins `c` of `A`. (Stated for any coin string `r` whose
encoding is `List.ofFn a ++ List.ofFn c`, so that any coin bijection can be used.) -/
theorem runAt_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (y : List Bool)
    {m : ℕ} (hm : m = p.eval n) (a : Fin m → Bool) (c : A.Coins n)
    (r : (A.wrap hpre hpost β b hβ p).Coins n) (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (A.wrap hpre hpost β b hβ p).runAt n y r =
      post (pairEncode (layout (List.replicate n true) y (List.ofFn a) (β n))
        (A.runAt n (pre (layout (List.replicate n true) y (List.ofFn a) (β n))) c)) := by
  rw [runAt_eq, runAtL_wrap, hr, List.take_left' (by simp [hm]), List.drop_left' (by simp [hm]),
    runAt_eq]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Reindexing the coins of an adversary -/

/-- Reindexing the coins of a distinguisher by a bijection does not change acceptance
probabilities. -/
theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : acceptProb X D = acceptProb X D' := by
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-- Reindexing the coins of a distinguisher by a bijection does not change PRG advantages. -/
theorem prgAdv_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype γ] [Fintype ρ] [Fintype ρ']
    (G : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : prgAdv G D = prgAdv G D' := by
  simp only [prgAdv_eq, distAdv_def]
  rw [acceptProb_coins_equiv G D D' e h, acceptProb_coins_equiv id D D' e h]

/-- Reindexing the coins of a predictor by a bijection does not change prediction
probabilities. -/
theorem predProb_coins_equiv {α β ρ ρ' : Type*} [Fintype α] [Fintype ρ] [Fintype ρ']
    (f : α → β) (B : α → Bool) (A : β → ρ → Bool) (A' : β → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ y c, A y (e c) = A' y c) : predProb f B A = predProb f B A' := by
  simp only [predProb_def]
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-! ## FP glue: cutting a string at the length of another -/

/-- `w ↦ (b w).take |a w|` is polynomial-time (`polyTimeComputable_pairTakePoly var` on
`⟨a w, b w⟩`). -/
theorem takeLen_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => (b w).take (a w).length := by
  convert (polyTimeComputable_pairTakePoly .var).comp (ha.pairEncode hb) using 1
  funext w
  simp

/-- `w ↦ (b w).drop |a w|` is polynomial-time (`polyTimeComputable_pairDropPoly var` on
`⟨a w, b w⟩`). -/
theorem dropLen_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => (b w).drop (a w).length := by
  convert (polyTimeComputable_pairDropPoly .var).comp (ha.pairEncode hb) using 1
  funext w
  simp

/-! ## Negligible functions times polynomials -/

/-- A syntactic polynomial times a negligible function is negligible
([Gar26, §1.2]; `Negligible.mul_pow` and `Negligible.const_mul` through the normal-form
majorant `C (n+1)^c ≤ C 2^c n^c` of `PolyExpr.eval_le`). -/
theorem Negligible.polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, c, hC⟩ := p.eval_le
  refine ((hμ.mul_pow c).const_mul ((C : ℝ) * 2 ^ c)).mono ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := by exact_mod_cast hC n
  have h2 : ((n : ℝ) + 1) ^ c ≤ (2 * (n : ℝ)) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  have hp : (p.eval n : ℝ) ≤ (C : ℝ) * 2 ^ c * (n : ℝ) ^ c :=
    calc (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := h1
      _ ≤ C * (2 * (n : ℝ)) ^ c := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (C : ℝ) * 2 ^ c * (n : ℝ) ^ c := by rw [_root_.mul_pow, mul_assoc]
  calc |(p.eval n : ℝ) * μ n| = (p.eval n : ℝ) * |μ n| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ (C : ℝ) * 2 ^ c * (n : ℝ) ^ c * |μ n| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = |(C : ℝ) * 2 ^ c * ((n : ℝ) ^ c * μ n)| := by
        rw [abs_mul ((C : ℝ) * 2 ^ c) ((n : ℝ) ^ c * μ n), abs_mul ((n : ℝ) ^ c) (μ n),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C : ℝ) * 2 ^ c),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ c), mul_assoc]

/-- The first `m` bits of the encoding of an `ℓ`-bit string (`m ≤ ℓ`) encode its restriction
along `Fin.castLE`. -/
theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i) := by
  refine List.ext_getElem (by simp [List.length_take, h]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  rfl

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## Parameter-aware pre-processing -/

/-- The raw function of the parameter-aware pre-processor on the layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`:
run `A.output` on `⟨⟨⟨1^n, pre ⟨1^n, y⟩⟩, α⟩, r⟩`. -/
def preFun (A : NUPPT) (pre : List Bool → List Bool) (z : List Bool) : List Bool :=
  A.output (layout (inParam z) (pre (pairEncode (inParam z) (inArg z))) (inAdvice z) (inCoins z))

/-- The raw function of the pre-processor is polynomial-time. -/
theorem preFun_poly (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    PolyTimeComputable (A.preFun pre) :=
  A.polyTimeComputable_output.comp (polyTimeComputable_layout polyTimeComputable_inParam
    (hpre.comp (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
    polyTimeComputable_inAdvice polyTimeComputable_inCoins)

/-- **Parameter-aware pre-processing** [PS10, §2.1, the closure properties used implicitly]:
the machine with `A`'s coins and advice computing `A(1^n, pre ⟨1^n, y⟩; r)`. Unlike
`NUPPT.exists_comp`, the pre-processing sees the parameter (needed to truncate an input to
`n + 1` bits). The coin type is definitionally `A.Coins n`. -/
noncomputable def preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : NUPPT :=
  ofPolyTime (A.preFun_poly hpre) A.coins A.adv A.advice A.advice_length

/-- The coin polynomial of the pre-processed machine is `A`'s. -/
@[simp] theorem coins_preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : (A.preComp hpre).coins = A.coins := by
  unfold preComp
  exact coins_ofPolyTime _ _ _ _ _

/-- **The pre-processed machine runs on the coins of `A`**: the published equivalence
`(A.preComp hpre).Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along `coins_preComp`). -/
noncomputable def preComp_coinsEquiv (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (n : ℕ) : (A.preComp hpre).Coins n ≃ A.Coins n :=
  coinsCongr (coins_preComp A hpre) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (A.preComp_coinsEquiv hpre n r) = List.ofFn r`. -/
theorem preComp_coinsEquiv_ofFn (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (n : ℕ) (r : (A.preComp hpre).Coins n) :
    List.ofFn (A.preComp_coinsEquiv hpre n r) = List.ofFn r :=
  coinsCongr_ofFn (coins_preComp A hpre) n r

/-- The untyped activation of the pre-processed machine. -/
theorem runAtL_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y r : List Bool) :
    (A.preComp hpre).runAtL n y r = A.runAtL n (pre (pairEncode (List.replicate n true) y)) r := by
  unfold preComp
  rw [runAtL_ofPolyTime]
  simp [preFun, runAtL_eq, advInput_eq, layout_eq, inParam_eq, inArg_eq, inAdvice_eq, inCoins_eq]

/-- The typed activation of the pre-processed machine, on the coins of `A` carried over by
`preComp_coinsEquiv`. -/
theorem runAt_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y : List Bool) (r : (A.preComp hpre).Coins n) :
    (A.preComp hpre).runAt n y r =
      A.runAt n (pre (pairEncode (List.replicate n true) y)) (A.preComp_coinsEquiv hpre n r) := by
  rw [runAt_eq, runAtL_preComp, runAt_eq, preComp_coinsEquiv_ofFn]

end Complexity.NUPPT
