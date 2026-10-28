/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.NextBit
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin
import TCSlib.Cryptography.HardcoreBit.ThreeQuarters
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine infrastructure for the hard-core predicate theorems

Proof infrastructure for `TCSlib.Cryptography.Asymptotic.HardCore` and
`TCSlib.Cryptography.Asymptotic.HardCorePermutation` ([PS10, Theorems 79.4 and 87.3,
Lemma 80.5]): the reductions of those theorems as `Complexity.NUPPT`s, built by the closure
calculus of `TCSlib.Complexity.Randomized` (foundation decision D2 of
`PassShelatChapter2-4Plan.md`), together with the bit-string identities and the probability
bookkeeping that identify each machine with the concrete reduction of the Garg layer.

* `Complexity.NUPPT.wrap` — the **one-call wrapper**: for a machine `A`, polynomial-time
  `pre`/`post`, an advice family `β` and a coin polynomial `p`, the machine that reads its
  first `p(n)` coins as data, pre-processes `⟨⟨⟨1^n, y⟩, coins⟩, β n⟩`, calls `A` once with
  the remaining coins and post-processes the answer. It packages every single-call reduction
  of the hard-core chapter (the predictor of Theorem 79.4, the hybrid distinguisher of
  Lemma 80.5, the padding inverters of Theorem 87.3, the pass-through-bit reductions of the
  balanced permutation).
* `TCSlib.Cryptography.prgIterFun` — the iterated evaluation of a one-bit-stretch generator
  (`Complexity.polyTimeComputable_iterateEmit`), for the expansion of Lemma 80.5.
* The small `List.ofFn` identities (`ofFn_snoc_eq`, `ofFn_appendEquiv`) and coin-split
  bijections used by all of them.

## Main definitions

* `Complexity.NUPPT.wrap`, `Complexity.NUPPT.wrapFun` — the one-call wrapper machine and
  its raw function.
* `TCSlib.Cryptography.prgIterStep`, `TCSlib.Cryptography.prgIterFun` — the iterated
  generator evaluation.

## Main results

* `Complexity.NUPPT.runAt_wrap` — the activation of the one-call wrapper on split coins.
* `TCSlib.Cryptography.prgIterFun_poly`, `TCSlib.Cryptography.prgIterFun_ofFn` — the
  iterated evaluation is polynomial-time and computes the output bits of the expansion.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4: Theorem 79.4; §3.3.5: Lemma 80.5; §3.4.2–3.4.3: Theorem 87.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3), §3.3 (Theorems 3.1, 3.2).
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
    (A.wrap hpre hpost β b hβ p).coins = .add p A.coins := rfl

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
  simp [wrapFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

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
  unfold acceptProb
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-- Reindexing the coins of a distinguisher by a bijection does not change PRG advantages. -/
theorem prgAdv_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype γ] [Fintype ρ] [Fintype ρ']
    (G : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : prgAdv G D = prgAdv G D' := by
  unfold prgAdv distAdv
  rw [acceptProb_coins_equiv G D D' e h, acceptProb_coins_equiv id D D' e h]

/-- Reindexing the coins of a predictor by a bijection does not change prediction
probabilities. -/
theorem predProb_coins_equiv {α β ρ ρ' : Type*} [Fintype α] [Fintype ρ] [Fintype ρ']
    (f : α → β) (B : α → Bool) (A : β → ρ → Bool) (A' : β → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ y c, A y (e c) = A' y c) : predProb f B A = predProb f B A' := by
  unfold predProb
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-! ## Theorem 79.4: the generator `f(s) ‖ h(s)` and its predictor -/

/-- **The evaluator of `f(s) ‖ h(s)`** from evaluators `F` of `f` and `H` of `h` on `⟨1^n, s⟩`:
`s ↦ F ⟨1^{|s|}, s⟩ ++ H ⟨1^{|s|}, s⟩` is polynomial-time and computes
`List.ofFn (Fin.snoc (f s) (h s))` (the efficiency clause of [PS10, Theorem 79.4]). -/
theorem exists_owpGenEvaluator (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    {F H : List Bool → List Bool} (hF : PolyTimeComputable F) (hH : PolyTimeComputable H)
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x))
    (hHx : ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
      ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (Fin.snoc (P.f n s) (h n s) : Fin (n + 1) → Bool) := by
  have hpre : PolyTimeComputable fun w : List Bool => pairEncode (List.replicate w.length true) w :=
    polyTimeComputable_unary.pairEncode polyTimeComputable_id
  refine ⟨fun w => F (pairEncode (List.replicate w.length true) w) ++
    H (pairEncode (List.replicate w.length true) w), (hF.comp hpre).append (hH.comp hpre),
    fun n s => ?_⟩
  have h1 := hFx n s
  have h2 := hHx n s
  simp only [NUPPT.advInput, List.length_ofFn] at h1 h2 ⊢
  rw [h1, h2, ofFn_snoc_eq]

/-- The pre-processing of the predictor of [PS10, Theorem 79.4]: on the view
`⟨⟨⟨1^n, y⟩, [σ]⟩, [flip]⟩` form the distinguisher's input `y ++ [σ]`. -/
def owpPredPre (w : List Bool) : List Bool := NUPPT.inArg w ++ NUPPT.inAdvice w

/-- The post-processing of the predictor of [PS10, Theorem 79.4]: on `⟨view, answer⟩` output
`[xor (if answer = [true] then σ else !σ) flip]`. -/
def owpPredPost (v : List Bool) : List Bool :=
  [xor (if pairSndD v = [true] then (NUPPT.inAdvice (pairFstD v)).headD false
    else !(NUPPT.inAdvice (pairFstD v)).headD false) ((NUPPT.inCoins (pairFstD v)).headD false)]

/-- The pre-processing of the predictor is polynomial-time. -/
theorem owpPredPre_poly : PolyTimeComputable owpPredPre :=
  NUPPT.polyTimeComputable_inArg.append NUPPT.polyTimeComputable_inAdvice

/-- The post-processing of the predictor is polynomial-time (`polyTimeComputable_pairEq` for
the verdict test, `StateLoop.headBit_poly` for the two bits, `polyTimeComputable_ite`,
`StateLoop.xor_poly`). -/
theorem owpPredPost_poly : PolyTimeComputable owpPredPost := by
  have htest : PolyTimeComputable fun v : List Bool => [decide (pairSndD v = [true])] := by
    convert polyTimeComputable_pairEq.comp
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [true])) using 1
    funext v
    simp
  have hσ : PolyTimeComputable fun v : List Bool =>
      [(NUPPT.inAdvice (pairFstD v)).headD false] :=
    StateLoop.headBit_poly.comp (NUPPT.polyTimeComputable_inAdvice.comp polyTimeComputable_pairFstD)
  have hflip : PolyTimeComputable fun v : List Bool =>
      [(NUPPT.inCoins (pairFstD v)).headD false] :=
    StateLoop.headBit_poly.comp (NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairFstD)
  have hite : PolyTimeComputable fun v : List Bool =>
      [if pairSndD v = [true] then (NUPPT.inAdvice (pairFstD v)).headD false
        else !(NUPPT.inAdvice (pairFstD v)).headD false] := by
    convert polyTimeComputable_ite htest hσ (StateLoop.not_poly hσ) using 1
    funext v
    by_cases hv : pairSndD v = [true] <;> simp [hv]
  exact StateLoop.xor_poly hite hflip

/-- **The predictor machine of [PS10, Theorem 79.4]** for a distinguisher `D` and a sign
family `flip`: advice `⟨[flip n], D.advice n⟩`, coins `1 + D.coins`; on `⟨1^n, y⟩` it reads the
first coin `σ`, calls `D(1^n, y ++ [σ])` with the remaining coins and outputs
`[xor (if D accepts then σ else !σ) (flip n)]` (`Complexity.NUPPT.wrap`). -/
noncomputable def owpPredMachine (D : NUPPT) (flip : ℕ → Bool) : NUPPT :=
  D.wrap owpPredPre_poly owpPredPost_poly (fun n => [flip n]) (.const 1)
    (fun _ => by simp) (.const 1)

/-- The predictor machine on coins `r = [σ] ++ c` computes the concrete predictor
`owpPredictor` of [Gar26, Theorem 3.2]: `xor (if D(y ‖ σ) then σ else !σ) flip`. -/
theorem owpPredMachine_predictor (D : NUPPT) (flip : ℕ → Bool) (n : ℕ) (y : Fin n → Bool)
    (σ : Bool) (c : D.Coins n) (r : (owpPredMachine D flip).Coins n)
    (hr : List.ofFn r = [σ] ++ List.ofFn c) :
    (owpPredMachine D flip).predictor n n y r =
      xor (if D.distinguisher n (n + 1) (Fin.snoc y σ) c then σ else !σ) (flip n) := by
  unfold owpPredMachine NUPPT.predictor NUPPT.distinguisher
  rw [NUPPT.runAt_wrap D owpPredPre_poly owpPredPost_poly (fun n => [flip n]) (.const 1)
    (fun _ => by simp) (.const 1) n (List.ofFn y) (m := 1) rfl (fun _ => σ) c r
    (by rw [hr]; rfl)]
  have h1 : List.ofFn (fun _ : Fin 1 => σ) = [σ] := by simp [List.ofFn_succ]
  simp only [owpPredPost, owpPredPre, pairSndD_pairEncode, pairFstD_pairEncode,
    NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.inCoins_layout, h1, List.headD_cons]
  rw [← ofFn_snoc_eq, NUPPT.runAt_eq]
  by_cases hD : D.runAtL n (List.ofFn (Fin.snoc y σ)) (List.ofFn c) = [true]
  · simp only [hD, if_true, decide_true]
    cases σ <;> cases flip n <;> rfl
  · simp only [hD, if_false, decide_false]
    cases σ <;> cases flip n <;> rfl

/-- **The prediction probability of the predictor machine** equals that of the concrete
predictor `owpPredictor` [Gar26, Theorem 3.2] run against `D(1^n, ·)` with the sign `flip n`,
for any `f` and `B` on `{0,1}^n`. -/
theorem owpPredMachine_predProb (D : NUPPT) (flip : ℕ → Bool) {n : ℕ}
    (f : (Fin n → Bool) → (Fin n → Bool)) (B : (Fin n → Bool) → Bool) :
    predProb f B ((owpPredMachine D flip).predictor n n) =
      predProb f B (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := by
  refine predProb_coins_equiv f B _ _
    (((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      (Fin.appendEquiv 1 (D.coinLen n))) fun y c => ?_
  obtain ⟨σ, c⟩ := c
  refine owpPredMachine_predictor D flip n y σ c _ ?_
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id]
  exact (ofFn_appendEquiv ((Equiv.funUnique (Fin 1) Bool).symm σ) c).trans
    (congrArg (· ++ List.ofFn c) (by simp [List.ofFn_succ]))

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Lemma 80.5: the iterated evaluation of a one-bit-stretch generator -/

/-- The seed update of the iterated evaluation: `w ↦ (F w).take |w|` (the first `|w|` bits of
the generator's output, the next seed `X_{i+1}` of [PS10, Lemma 80.5]). -/
def prgIterStep (F : List Bool → List Bool) (w : List Bool) : List Bool := (F w).take w.length

/-- The emitted bit of the iterated evaluation: `w ↦ (F w).drop |w|` (the last bit of the
generator's output, the bit `b_{i+1}` of [PS10, Lemma 80.5]). -/
def prgIterEmit (F : List Bool → List Bool) (w : List Bool) : List Bool := (F w).drop w.length

/-- The iterated evaluation: the output bits of `ℓ(|s|) + 1` rounds of the generator from the
seed `s`, concatenated (`Complexity.polyTimeComputable_iterateEmit`). -/
def prgIterFun (F : List Bool → List Bool) (ℓ : PolyExpr) (s : List Bool) : List Bool :=
  (List.range (ℓ.eval s.length + 1)).flatMap fun i => prgIterEmit F ((prgIterStep F)^[i] s)

/-- The seed update is polynomial-time (`polyTimeComputable_pairTakePoly var` on `⟨w, F w⟩`). -/
theorem prgIterStep_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgIterStep F) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (polyTimeComputable_id.pairEncode hF) using 1
  funext w
  simp [prgIterStep]

/-- The emitted bit is polynomial-time (`polyTimeComputable_pairDropPoly var` on `⟨w, F w⟩`). -/
theorem prgIterEmit_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgIterEmit F) := by
  convert (polyTimeComputable_pairDropPoly .var).comp (polyTimeComputable_id.pairEncode hF) using 1
  funext w
  simp [prgIterEmit]

/-- The seed update never lengthens a word, so its orbit stays within the input length. -/
theorem length_prgIterStep_iterate_le (F : List Bool → List Bool) (w : List Bool) (i : ℕ) :
    ((prgIterStep F)^[i] w).length ≤ w.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (List.length_take_le _ _).trans ih

/-- **The iterated evaluation is polynomial-time** (instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := ℓ` and orbit bound `P := var`). -/
theorem prgIterFun_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    PolyTimeComputable (prgIterFun F ℓ) :=
  polyTimeComputable_iterateEmit (prgIterStep_poly hF) (prgIterEmit_poly hF) ℓ .var
    (fun x i _ => length_prgIterStep_iterate_le F x i)

section Generator

variable (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) {F : List Bool → List Bool}
  (hFs : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s))

include hFs

/-- On an encoded seed the seed update computes the first `n` bits of `G(s)`. -/
theorem prgIterStep_ofFn (n : ℕ) (s : Fin n → Bool) :
    prgIterStep F (List.ofFn s) = List.ofFn (Fin.init (G n s)) := by
  unfold prgIterStep
  rw [hFs, List.length_ofFn, ofFn_eq_init_append, List.take_left' List.length_ofFn]

/-- On an encoded seed the emitted bit is the last bit of `G(s)`. -/
theorem prgIterEmit_ofFn (n : ℕ) (s : Fin n → Bool) :
    prgIterEmit F (List.ofFn s) = [G n s (Fin.last n)] := by
  unfold prgIterEmit
  rw [hFs, List.length_ofFn, ofFn_eq_init_append, List.drop_left' List.length_ofFn]

/-- The iterates of the seed update on an encoded seed are the encoded iterates of
`s ↦ init (G s)`. -/
theorem prgIterStep_iterate_ofFn (n : ℕ) (s : Fin n → Bool) (i : ℕ) :
    (prgIterStep F)^[i] (List.ofFn s) = List.ofFn ((fun x => Fin.init (G n x))^[i] s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, prgIterStep_ofFn G hFs, Function.iterate_succ_apply']

/-- **The iterated evaluation on an encoded seed** is the string of the `ℓ(n) + 1` output bits
`G(X_i)_{last}`, `X_i` the `i`-th iterate of `s ↦ init (G s)`. -/
theorem prgIterFun_ofFn (ℓ : PolyExpr) (n : ℕ) (s : Fin n → Bool) :
    prgIterFun F ℓ (List.ofFn s) =
      List.ofFn fun i : Fin (ℓ.eval n + 1) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  unfold prgIterFun
  rw [List.length_ofFn]
  refine List.ext_getElem (by simp [List.length_flatMap, prgIterStep_iterate_ofFn G hFs,
    prgIterEmit_ofFn G hFs]) fun j hj₁ hj₂ => ?_
  have hmap : ((List.range (ℓ.eval n + 1)).flatMap fun i =>
      prgIterEmit F ((prgIterStep F)^[i] (List.ofFn s))) =
      (List.range (ℓ.eval n + 1)).map fun i => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
    rw [List.map_eq_flatMap]
    congr 1
    funext i
    rw [prgIterStep_iterate_ofFn G hFs, prgIterEmit_ofFn G hFs]
  simp only [hmap, List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- The first `ℓ(n)` bits of the iterated evaluation: the output of the expansion `G'` of
[PS10, Lemma 80.5]. -/
theorem take_prgIterFun_ofFn (ℓ : PolyExpr) (n : ℕ) (s : Fin n → Bool) :
    (prgIterFun F ℓ (List.ofFn s)).take (ℓ.eval n) =
      List.ofFn fun i : Fin (ℓ.eval n) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  rw [prgIterFun_ofFn G hFs, List.ofFn_succ', List.concat_eq_append,
    List.take_left' List.length_ofFn]
  rfl

/-- **The evaluator of the expansion `G'`** [PS10, Lemma 80.5, "`G'` is efficiently
computable"]: `s ↦ (prgIterFun F ℓ s).take (ℓ |s|)` is polynomial-time and computes the
`ℓ(n)` output bits. -/
theorem exists_expandEvaluator (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧ ∀ n (s : Fin n → Bool),
      E (List.ofFn s) =
        List.ofFn fun i : Fin (ℓ.eval n) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  refine ⟨fun w => (prgIterFun F ℓ w).take (ℓ.eval w.length), ?_, fun n s => ?_⟩
  · convert (polyTimeComputable_pairTakePoly ℓ).comp
      (polyTimeComputable_id.pairEncode (prgIterFun_poly hF ℓ)) using 1
    funext w
    simp
  · dsimp only
    rw [List.length_ofFn, take_prgIterFun_ofFn G hFs]

end Generator

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

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

/-! ## Lemma 80.5: the hybrid distinguisher -/

/-- The pre-processing of the hybrid-`k` reduction of [PS10, Lemma 80.5] on the view
`⟨⟨⟨1^n, T⟩, c⟩, ⟨1^k, 1^{ℓ−k−1}⟩⟩`: the `ℓ`-bit string
`c.take k ++ T.drop n ++ (prgIterFun F ℓ (T.take n)).take (ℓ − k − 1)` — `k` uniform bits,
the given bit `T_{n+1}`, and `ℓ − k − 1` bits generated from the given seed `T_1 ⋯ T_n`. -/
def expandRedPre (F : List Bool → List Bool) (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (NUPPT.inAdvice w).take (pairFstD (NUPPT.inCoins w)).length ++
    (NUPPT.inArg w).drop (NUPPT.inParam w).length ++
    (prgIterFun F ℓ ((NUPPT.inArg w).take (NUPPT.inParam w).length)).take
      (pairSndD (NUPPT.inCoins w)).length

/-- The pre-processing of the hybrid reduction is polynomial-time. -/
theorem expandRedPre_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    PolyTimeComputable (expandRedPre F ℓ) :=
  ((takeLen_poly (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inCoins)
    NUPPT.polyTimeComputable_inAdvice).append
      (dropLen_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg)).append
    (takeLen_poly (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inCoins)
      ((prgIterFun_poly hF ℓ).comp
        (takeLen_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg)))

/-- **The hybrid-`k` distinguisher machine of [PS10, Lemma 80.5]** for a distinguisher `D` of
the expansion, a hybrid index family `k n < ℓ(n)` and the evaluator `F` of the generator:
advice `⟨⟨1^{k n}, 1^{ℓ(n) − k n − 1}⟩, D.advice n⟩`, coins `ℓ + D.coins`; on `⟨1^n, T⟩` it forms
the `ℓ(n)`-bit hybrid string (`expandRedPre`) and returns `D`'s verdict on it
(`Complexity.NUPPT.wrap`). -/
noncomputable def expandRedMachine (D : NUPPT) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F) (ℓ : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, k n < ℓ.eval n) : NUPPT :=
  D.wrap (expandRedPre_poly hF ℓ) polyTimeComputable_pairSndD
    (fun n => pairEncode (List.replicate (k n) true) (List.replicate (ℓ.eval n - k n - 1) true))
    (.add (.mul (.const 3) ℓ) (.const 2)) (fun n => by
      rw [length_pairEncode, List.length_replicate, List.length_replicate]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := hk n
      omega) ℓ

section Generator

variable (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) {F : List Bool → List Bool}
  (hFs : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s))

include hFs

/-- **The hybrid string** formed by `expandRedPre` on the view of `⟨1^n, T⟩` with data coins
`a` and advice `⟨1^k, 1^{ℓ−k−1}⟩` is the input of the concrete hybrid distinguisher
[Gar26, Theorem 3.1]: bit `i` is `a_i` for `i < k`, the given bit `T_{last}` at `i = k`, and
`G(X_{i−k−1})_{last}` beyond, with `X_j` the `j`-th iterate of `s ↦ init (G s)` on `init T`. 

**Proof sketch.** Unfold the projections of the view; `T` splits as `init T ‖ [T_last]` (`ofFn_eq_init_append`) and the iterated evaluation is `prgIterFun_ofFn`; then `List.ext_getElem` with the three index ranges `i < k`, `i = k`, `i > k` (`List.getElem_append_left/right`, `List.getElem_take`, `List.getElem_ofFn`). -/
theorem expandRedPre_layout (ℓ : PolyExpr) (n k : ℕ) (hk : k < ℓ.eval n) (T : Fin (n + 1) → Bool)
    (a : Fin (ℓ.eval n) → Bool) :
    expandRedPre F ℓ (NUPPT.layout (List.replicate n true) (List.ofFn T) (List.ofFn a)
      (pairEncode (List.replicate k true) (List.replicate (ℓ.eval n - k - 1) true))) =
    List.ofFn fun i : Fin (ℓ.eval n) => if (i : ℕ) < k then a i else if (i : ℕ) = k then T (Fin.last n)
      else G n ((fun x => Fin.init (G n x))^[i - k - 1] (Fin.init T)) (Fin.last n) := by
  simp only [expandRedPre, NUPPT.inAdvice_layout, NUPPT.inCoins_layout, NUPPT.inArg_layout,
    NUPPT.inParam_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  rw [ofFn_eq_init_append T, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    prgIterFun_ofFn G hFs]
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_append, List.length_take, List.length_ofFn, List.length_singleton]
    omega
  · simp only [List.length_ofFn] at hj₂
    simp only [List.getElem_ofFn]
    by_cases h1 : j < k
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_take, List.getElem_ofFn]
      simp [h1]
    · by_cases h2 : j = k
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp [h2]
      · rw [List.getElem_append_right (by simp; omega), List.getElem_take, List.getElem_ofFn]
        simp only [h1, h2, if_false, List.length_append, List.length_take, List.length_ofFn,
          List.length_singleton]
        rw [show j - (min k (ℓ.eval n) + 1) = j - k - 1 by omega]

/-- **The hybrid distinguisher machine computes the concrete hybrid reduction**: on coins
`r = a ++ c` its verdict on `T` is `D`'s verdict on the hybrid string with uniform bits `a`
and coins `c`. -/
theorem expandRedMachine_distinguisher (D : NUPPT) (hF : PolyTimeComputable F) (ℓ : PolyExpr)
    (k : ℕ → ℕ) (hk : ∀ n, k n < ℓ.eval n) (n : ℕ) (T : Fin (n + 1) → Bool)
    (a : Fin (ℓ.eval n) → Bool) (c : D.Coins n) (r : (expandRedMachine D hF ℓ k hk).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (expandRedMachine D hF ℓ k hk).distinguisher n (n + 1) T r =
      D.distinguisher n (ℓ.eval n) (fun i => if (i : ℕ) < k n then a i
        else if (i : ℕ) = k n then T (Fin.last n)
        else G n ((fun x => Fin.init (G n x))^[i - k n - 1] (Fin.init T)) (Fin.last n)) c := by
  unfold expandRedMachine NUPPT.distinguisher
  rw [NUPPT.runAt_wrap D (expandRedPre_poly hF ℓ) polyTimeComputable_pairSndD _ _ _ ℓ n
    (List.ofFn T) rfl a c r hr, pairSndD_pairEncode, expandRedPre_layout G hFs ℓ n (k n) (hk n) T a]

end Generator

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Theorem 87.3, first clause: the padded family `g(x, r) = (f(x), r)` is one-way -/

/-- **The evaluator of `g(x, r) = (f(x), r)`** [PS10, Theorem 87.3, "`g` is easy to compute"]
from an evaluator `F` of `f` on `⟨1^n, x⟩`: on `⟨1^n, x ‖ r⟩` output
`F ⟨1^n, (x ‖ r).take (inLen n)⟩ ++ (x ‖ r).drop (inLen n)`. -/
theorem exists_glPadEvaluator (𝓕 : FunFamily) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (hFx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
      F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
      ∀ n (x r : Fin (𝓕.inLen.eval n) → Bool),
        E (NUPPT.advInput n (List.ofFn x ++ List.ofFn r)) = List.ofFn (𝓕.f n x) ++ List.ofFn r := by
  refine ⟨fun w => F (pairEncode (pairFstD w)
      ((pairSndD w).take (𝓕.inLen.eval (pairFstD w).length))) ++
      (pairSndD w).drop (𝓕.inLen.eval (pairFstD w).length),
    (hF.comp (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly 𝓕.inLen))).append
      (polyTimeComputable_pairDropPoly 𝓕.inLen), fun n x r => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    take_ofFn_append, drop_ofFn_append]
  rw [← NUPPT.advInput, hFx]

/-- The post-processing of the padding inverter of [PS10, Theorem 87.3]: on `⟨view, answer⟩`
keep the first `|r|` bits of the answer, `r` the coin head of the view (the string `x'` of the
answer `x' ‖ r'`). -/
def glPadInvPost (v : List Bool) : List Bool :=
  (pairSndD v).take (NUPPT.inAdvice (pairFstD v)).length

/-- The post-processing of the padding inverter is polynomial-time. -/
theorem glPadInvPost_poly : PolyTimeComputable glPadInvPost :=
  takeLen_poly (NUPPT.polyTimeComputable_inAdvice.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairSndD

/-- **The padding inverter machine of [PS10, Theorem 87.3]** (`OneWay.padInverter` of
[Gar26, Lemma 2.3] at the machine level): for an inverter `A` of `g(x, r) = (f(x), r)` and the
padding length `p`, the machine with coins `p + A.coins` and `A`'s advice that, on `⟨1^n, y⟩`,
reads its first `p(n)` coins as the padding `r`, calls `A(1^n, y ++ r)` with the remaining coins
and returns the first `p(n)` bits of the answer (`Complexity.NUPPT.wrap`; the pre-processing
`y ++ r` is `owpPredPre`). -/
noncomputable def glPadInvMachine (A : NUPPT) (p : PolyExpr) : NUPPT :=
  A.wrap owpPredPre_poly glPadInvPost_poly (fun _ => []) (.const 0) (fun _ => by simp) p

/-- The padding inverter on coins `r = a ++ c` returns the first `p(n)` bits of
`A(1^n, y ++ a; c)`. -/
theorem glPadInvMachine_runAt (A : NUPPT) (p : PolyExpr) (n : ℕ) (y : List Bool)
    (a : Fin (p.eval n) → Bool) (c : A.Coins n) (r : (glPadInvMachine A p).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (glPadInvMachine A p).runAt n y r = (A.runAt n (y ++ List.ofFn a) c).take (p.eval n) := by
  unfold glPadInvMachine
  rw [NUPPT.runAt_wrap A owpPredPre_poly glPadInvPost_poly _ _ _ p n y rfl a c r hr]
  simp [glPadInvPost, owpPredPre]

/-- **The padding inverter inverts `f` at least as often as `A` inverts `g`**
([PS10, Theorem 87.3], first clause; [Gar26, Lemma 2.3]): at every `n`, the inversion
probability of `A` against `g_n = appendEquiv ∘ HardcoreBit.glPad (f n) ∘ appendEquiv⁻¹` on
`{0,1}^{2·inLen n}` is at most that of `glPadInvMachine A inLen` against `f n`.

**Proof sketch.** Reindex the inputs by `appendEquiv` and the coins of the padding inverter by
`appendEquiv`, regroup by `Equiv.prodAssoc` and compare pointwise (`uprob_mono`): if `A`'s
answer `x' ‖ r'` satisfies `f(x') ‖ r' = f(x) ‖ r` then `f(x') = f(x)` (`Fin.appendEquiv` is
injective) and the padding inverter returns exactly `x'`. -/
theorem invProbOpt_glPad_le (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) :
    invProbOpt (fun z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool =>
        Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
          (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)))
      (A.inverter n (𝓕.inLen.eval n + 𝓕.inLen.eval n) (𝓕.outLen.eval n + 𝓕.inLen.eval n)) ≤
    invProbOpt (𝓕.f n)
      ((glPadInvMachine A 𝓕.inLen).inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n)) := by
  unfold invProbOpt
  refine le_of_eq_of_le (uprob_comp_equiv
    ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).prodCongr (Equiv.refl (A.Coins n))) _).symm ?_
  refine le_of_le_of_eq ?_ ((uprob_comp_equiv
    (Equiv.prodAssoc (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.inLen.eval n) → Bool) (A.Coins n)) _).trans
    (uprob_comp_equiv ((Equiv.refl (Fin (𝓕.inLen.eval n) → Bool)).prodCongr
      (Fin.appendEquiv (𝓕.inLen.eval n) (A.coinLen n))) _))
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨x, r⟩, c⟩ := w
  obtain ⟨x', hx', hfx'⟩ := hw
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, Equiv.symm_apply_apply,
    Equiv.prodAssoc_apply, NUPPT.inverter_eq_some_iff] at hx' hfx' ⊢
  obtain ⟨⟨x'', r''⟩, rfl⟩ := (Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).surjective x'
  simp only [Equiv.symm_apply_apply] at hfx' hx'
  have hpair := (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).injective
    (show Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n) (x'', r'')) =
      Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n) (x, r)) from hfx')
  simp only [HardcoreBit.glPad, Prod.mk.injEq] at hpair
  refine ⟨x'', ?_, hpair.1⟩
  rw [glPadInvMachine_runAt A 𝓕.inLen n _ r c _ (ofFn_appendEquiv r c)]
  simp only [HardcoreBit.glPad] at hx'
  rw [ofFn_appendEquiv, ofFn_appendEquiv] at hx'
  rw [hx', take_ofFn_append]

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Theorem 87.3 for collections, first clause: the padded collection is one-way -/

/-- The decoder of the padded collection `g_i(x, r) = ⟨f_i(x), r⟩` (the `decD` of
`Collection.glPad`): split the string as a pair, decode the first component with `decD i` and
the second as an `L`-bit string. -/
def glPadDecode (F : Collection) (i : List Bool) (L : ℕ) (w : List Bool) :
    Option (F.D i × (Fin L → Bool)) :=
  match pairDecode w with
  | some (a, b) => match F.decD i a, decodeFin L b with
    | some x, some r => some (x, r)
    | _, _ => none
  | none => none

/-- Decoding `⟨a, ofFn s⟩`: the first component decoded by `decD i`, paired with `s`. -/
theorem glPadDecode_pairEncode_ofFn (F : Collection) (i : List Bool) {L : ℕ} (a : List Bool)
    (s : Fin L → Bool) :
    glPadDecode F i L (pairEncode a (List.ofFn s)) = (F.decD i a).map fun x => (x, s) := by
  cases h : F.decD i a <;> simp [glPadDecode, pairDecode_pairEncode, decodeFin_ofFn, h]

/-- A successful decoding `glPadDecode F i L w = some (x, s)` means `w = ⟨a, b⟩` with
`decD i a = some x` (and `b` the encoding of `s`). -/
theorem glPadDecode_eq_some (F : Collection) (i : List Bool) {L : ℕ} (w : List Bool)
    {x : F.D i} {s : Fin L → Bool} (h : glPadDecode F i L w = some (x, s)) :
    ∃ a b, w = pairEncode a b ∧ F.decD i a = some x ∧ decodeFin L b = some s := by
  unfold glPadDecode at h
  cases hw : pairDecode w with
  | none => simp [hw] at h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    refine ⟨a, b, eq_pairEncode_of_pairDecode w a b hw, ?_⟩
    simp only [hw] at h
    cases ha : F.decD i a <;> cases hb : decodeFin L b <;> simp [ha, hb] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

/-- **The sampler of the padded collection is close to uniform** ([PS10, Theorem 87.3],
collection form, clause (2)): if a sampler `S` with coins `Sample.coins + m` runs `Sample` on
its first coins and appends the remaining `m(n)` coins, and `Sample` is `δ`-close to uniform on
`D_i`, then the decoded output of `S` is `δ`-close to uniform on `D_i × {0,1}^L` (`L = m(n)`).

**Proof sketch.** `StatClose.prod` of the closeness of `Sample` with the exact uniformity of the
padding, mapped through `(o, s) ↦ o.map (·, s)` (`StatClose.map`) and transported along the coin
split `appendEquiv` (`StatClose.comp_equiv_left`); the decoder on `⟨a, ofFn s⟩` is
`glPadDecode_pairEncode_ofFn`. -/
theorem statClose_glPadSampler (F : Collection) (m : PolyExpr) (S : NUPPT)
    (hS : S.coins = .add F.sample.coins m)
    (hrun : ∀ n i r, S.runAtL n i r =
      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)))
    {δ : ℕ → ℝ} (hclose : F.SampleClose δ) (n : ℕ) (r : F.gen.Coins n) (L : ℕ) (hL : L = m.eval n) :
    StatClose (fun s : S.Coins n => glPadDecode F (F.index n r) L (S.runAt n (F.index n r) s))
      (fun x : F.D (F.index n r) × (Fin L → Bool) => some x) (δ n) := by
  have hlen : F.sample.coinLen n + L = S.coinLen n := by
    show F.sample.coinLen n + L = S.coins.eval n
    rw [hS, PolyExpr.eval_add, hL]; rfl
  let e : F.sample.Coins n × (Fin L → Bool) ≃ S.Coins n :=
    (Fin.appendEquiv _ _).trans (finCastEquiv hlen)
  have h0 : StatClose (fun s : Fin L → Bool => s) (fun s : Fin L → Bool => s) 0 := StatClose.refl _
  have h1 := ((hclose n r).prod h0).map
    (fun z : Option (F.D (F.index n r)) × (Fin L → Bool) => z.1.map fun x => (x, z.2))
  rw [add_zero] at h1
  have h2 := h1.comp_equiv_left e.symm
  convert h2 using 1
  · funext s
    obtain ⟨⟨s₁, s₂⟩, rfl⟩ := e.surjective s
    have hofn : List.ofFn (e (s₁, s₂)) = List.ofFn s₁ ++ List.ofFn s₂ := by
      simp only [e, Equiv.trans_apply]
      rw [ofFn_finCastEquiv, ofFn_appendEquiv]
    simp only [NUPPT.runAt_eq, hrun, hofn, take_ofFn_append, drop_ofFn_append,
      glPadDecode_pairEncode_ofFn, Equiv.symm_apply_apply]

/-- The pre-processing of the inverter of the padded collection: on the view
`⟨⟨⟨1^n, ⟨i, y⟩⟩, r⟩, []⟩` form `A`'s input `⟨i, ⟨y, r⟩⟩`. -/
def glPadCollPre (w : List Bool) : List Bool :=
  pairEncode (pairFstD (NUPPT.inArg w)) (pairEncode (pairSndD (NUPPT.inArg w)) (NUPPT.inAdvice w))

/-- The pre-processing of the collection inverter is polynomial-time. -/
theorem glPadCollPre_poly : PolyTimeComputable glPadCollPre :=
  (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
    ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      NUPPT.polyTimeComputable_inAdvice)

/-- The post-processing of the collection inverter: the first component of `A`'s answer. -/
def glPadCollPost (v : List Bool) : List Bool := pairFstD (pairSndD v)

/-- The post-processing of the collection inverter is polynomial-time. -/
theorem glPadCollPost_poly : PolyTimeComputable glPadCollPost :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The inverter of the padded collection** ([PS10, Theorem 87.3], collection form): for an
inverter `A` of `g_i(x, r) = ⟨f_i(x), r⟩` and the padding length `m`, the machine with coins
`m + A.coins` and `A`'s advice that, on `⟨1^n, ⟨i, y⟩⟩`, reads its first `m(n)` coins as the
padding `r`, calls `A(1^n, ⟨i, ⟨y, r⟩⟩)` with the remaining coins and returns the first component
of the answer (`Complexity.NUPPT.wrap`). -/
noncomputable def glPadCollInvMachine (A : NUPPT) (m : PolyExpr) : NUPPT :=
  A.wrap glPadCollPre_poly glPadCollPost_poly (fun _ => []) (.const 0) (fun _ => by simp) m

/-- The collection inverter on coins `r = a ++ c` returns the first component of
`A(1^n, ⟨i, ⟨y, a⟩⟩; c)`. -/
theorem glPadCollInvMachine_runAt (A : NUPPT) (m : PolyExpr) (n : ℕ) (i y : List Bool)
    (a : Fin (m.eval n) → Bool) (c : A.Coins n) (r : (glPadCollInvMachine A m).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (glPadCollInvMachine A m).runAt n (pairEncode i y) r =
      pairFstD (A.runAt n (pairEncode i (pairEncode y (List.ofFn a))) c) := by
  unfold glPadCollInvMachine
  rw [NUPPT.runAt_wrap A glPadCollPre_poly glPadCollPost_poly _ _ _ m n (pairEncode i y) rfl a c r hr]
  simp [glPadCollPost, glPadCollPre]

/-- **The collection inverter inverts `F` at least as often as `A` inverts the padded
collection** ([PS10, Theorem 87.3], collection form, first clause): the inversion experiment of
`A` against `g_i(x, r) = ⟨f_i(x), r⟩` (with the padding of length `L r = m(n)` and the decoder
`glPadDecode`) is at most `F.invProbAt (glPadCollInvMachine A m) n`.

**Proof sketch.** Pointwise in the generator's coins (`OneWay.uexp_mono`); for a fixed index
reindex the padding by `L r = m(n)` and the coins of the collection inverter by `appendEquiv`,
regroup by `Equiv.prodAssoc` and compare pointwise (`uprob_mono`): a decoded answer `(x', r')`
with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)` (`pairDecode_pairEncode`), and the
collection inverter returns the first component `a` of `A`'s answer `⟨a, b⟩`, which decodes to
`x'` (`glPadDecode_eq_some`). -/
theorem glPad_invProbAt_le (F : Collection) (m : PolyExpr) (A : NUPPT) (n : ℕ)
    (L : F.gen.Coins n → ℕ) (hL : ∀ r, L r = m.eval n) :
    uexp (fun r : F.gen.Coins n =>
      uprob fun z : (F.D (F.index n r) × (Fin (L r) → Bool)) × A.Coins n =>
        ∃ x', glPadDecode F (F.index n r) (L r)
            (A.runAt n (pairEncode (F.index n r)
              (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
          pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) =
            pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2)) ≤
    F.invProbAt (glPadCollInvMachine A m) n := by
  unfold Collection.invProbAt
  refine OneWay.uexp_mono fun r => ?_
  refine le_of_eq_of_le (uprob_comp_equiv
    (((Equiv.refl (F.D (F.index n r))).prodCongr (finCastEquiv (hL r).symm)).prodCongr
        (Equiv.refl (A.Coins n))) _).symm ?_
  refine le_of_le_of_eq ?_ ((uprob_comp_equiv
    (Equiv.prodAssoc (F.D (F.index n r)) (Fin (m.eval n) → Bool) (A.Coins n)) _).trans
    (uprob_comp_equiv ((Equiv.refl (F.D (F.index n r))).prodCongr
      (Fin.appendEquiv (m.eval n) (A.coinLen n))) _))
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨x, ρ⟩, c⟩ := w
  obtain ⟨⟨x', ρ'⟩, hx', hfx'⟩ := hw
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, Equiv.prodAssoc_apply,
    ofFn_finCastEquiv] at hx' hfx' ⊢
  have hf : F.f (F.index n r) x' = F.f (F.index n r) x := by
    have := congrArg pairDecode hfx'
    simp only [pairDecode_pairEncode, Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  obtain ⟨a, b, hab, ha, -⟩ := glPadDecode_eq_some F (F.index n r) _ hx'
  refine ⟨x', ?_, hf⟩
  rw [glPadCollInvMachine_runAt A m n _ _ ρ c _ (ofFn_appendEquiv ρ c), hab, pairFstD_pairEncode, ha]

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## The parameter-change machine as a definition -/

/-- **The parameter-change machine `n ↦ p(n)`** (the witness of `exists_reparam`, as a
definition so that its coins and activation are available by `rfl`): advice `A.advice (p n)`,
coins `A.coins.subst p`; on `⟨1^n, y⟩` it replaces the unary parameter by `1^{p(n)}`
(`polyTimeComputable_unaryPoly p`) and runs `A`. -/
noncomputable def reparam (A : NUPPT) (p : PolyExpr) : NUPPT :=
  ofPolyTime (A.polyTimeComputable_output.comp
    (polyTimeComputable_layout ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_inParam)
      polyTimeComputable_inArg polyTimeComputable_inAdvice polyTimeComputable_inCoins))
    (A.coins.subst p) (A.adv.subst p) (fun n => A.advice (p.eval n)) (fun n => by
      rw [PolyExpr.eval_subst]
      exact A.advice_length _)

/-- The coin polynomial of the parameter-change machine is `A.coins.subst p`. -/
@[simp] theorem coins_reparam (A : NUPPT) (p : PolyExpr) : (A.reparam p).coins = A.coins.subst p :=
  rfl

/-- The parameter-change machine at `n` behaves as `A` at `p(n)`. -/
theorem runAtL_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) (y r : List Bool) :
    (A.reparam p).runAtL n y r = A.runAtL (p.eval n) y r := by
  unfold reparam
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- The number of coins of the parameter-change machine at `n` is that of `A` at `p(n)`. -/
theorem coinLen_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) :
    (A.reparam p).coinLen n = A.coinLen (p.eval n) := by
  simp [coinLen, PolyExpr.eval_subst]

/-- The coins of `A` at `p(n)` as the coins of the parameter-change machine at `n`. -/
noncomputable def reparamCoins (A : NUPPT) (p : PolyExpr) (n : ℕ) :
    A.Coins (p.eval n) ≃ (A.reparam p).Coins n :=
  TCSlib.Cryptography.finCastEquiv (coinLen_reparam A p n).symm

/-- The typed activation of the parameter-change machine. -/
theorem runAt_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) (y : List Bool) (c : A.Coins (p.eval n)) :
    (A.reparam p).runAt n y (reparamCoins A p n c) = A.runAt (p.eval n) y c := by
  rw [runAt_eq, runAtL_reparam, reparamCoins, TCSlib.Cryptography.ofFn_finCastEquiv, runAt_eq]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Helpers of the padded families and collections (`Asymptotic/HardCore.lean`) -/

/-- The re-encoding `(x ‖ r, c) ↦ ((x, r), c)` of the experiments. -/
def splitPair (a b : ℕ) (ρ : Type*) :
    (Fin (a + b) → Bool) × ρ ≃ ((Fin a → Bool) × (Fin b → Bool)) × ρ where
  toFun z := ((Fin.appendEquiv a b).symm z.1, z.2)
  invFun z := (Fin.appendEquiv a b z.1, z.2)
  left_inv z := Prod.ext ((Fin.appendEquiv a b).apply_symm_apply z.1) rfl
  right_inv z := Prod.ext ((Fin.appendEquiv a b).symm_apply_apply z.1) rfl

namespace Collection

variable (F : Collection)

/-- The raw sampler of the padded collection on the layout `⟨⟨⟨1^n, i⟩, []⟩, r⟩`: run the
domain sampler of `F` on the first `|Sample's coins|` coins and append the remaining coins
as the padding `r`. -/
def glPadSampleFun (z : List Bool) : List Bool :=
  pairEncode
    (F.sample.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) []
      ((pairSndD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).take
        (F.sample.coins.eval (pairFstD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).length))))
    ((pairSndD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).drop
      (F.sample.coins.eval (pairFstD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).length))

/-- The raw sampler of the padded collection is polynomial-time (pairing calculus,
`polyTimeComputable_pairTakePoly`/`pairDropPoly`, the sampler's own output function). -/
theorem glPadSampleFun_poly : PolyTimeComputable (glPadSampleFun F) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have htake := (polyTimeComputable_pairTakePoly F.sample.coins).comp hcut
  have hdrop := (polyTimeComputable_pairDropPoly F.sample.coins).comp hcut
  exact (F.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      NUPPT.polyTimeComputable_inArg (polyTimeComputable_const []) htake)).pairEncode hdrop

/-- The activation of the padded sampler on the index `i` with coins `s`, stated on the
machine (so that `glPad` can discharge `sample_spec`): `Sample(1^n, i)` on the first
`|Sample's coins|` coins paired with the remaining coins. -/
theorem glPadSample_runAt (m : PolyExpr) (n : ℕ) (i : List Bool)
    (s : (NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)).Coins n) :
    (NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)).runAt n i s =
      pairEncode (F.sample.runAtL n i ((List.ofFn s).take (F.sample.coinLen n)))
        ((List.ofFn s).drop (F.sample.coinLen n)) := by
  simp only [NUPPT.runAt, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
    NUPPT.coinLen, NUPPT.runAtL]

end Collection

/-- The raw trapdoor inverter of the padded collection on the layout
`⟨⟨⟨1^n, ⟨t, ⟨y, r⟩⟩⟩, []⟩, s⟩`: run `Inv(1^n, ⟨t, y⟩; s)` and append `r`. -/
def glPadInvFun (T : TrapdoorCollection) (z : List Bool) : List Bool :=
  pairEncode
    (T.inv.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))) []
      (NUPPT.inCoins z)))
    (pairSndD (pairSndD (NUPPT.inArg z)))

/-- The raw trapdoor inverter of the padded collection is polynomial-time. -/
theorem glPadInvFun_poly (T : TrapdoorCollection) : PolyTimeComputable (glPadInvFun T) :=
  (T.inv.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
        NUPPT.polyTimeComputable_inArg)))
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)).pairEncode
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      NUPPT.polyTimeComputable_inArg))

end TCSlib.Cryptography
