/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.NextBit
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin
import TCSlib.Cryptography.HardcoreBit.ThreeQuarters
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.StretchMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine reductions for hard-core predicates

This file constructs the predictor used for the permutation generator and
the inverters for the Goldreich–Levin padding. The shared wrapper and the stretch
machine are available through the existing import.

## Main definitions

* `TCSlib.Cryptography.owpPredMachine` gives the predictor from a distinguisher.
* `TCSlib.Cryptography.glPadInvMachine` gives the padding inverter.

## Main results

* `TCSlib.Cryptography.owpPredMachine_predictor` identifies the machine's verdict.
* `TCSlib.Cryptography.glPadInvMachine_runAt` gives the padding inverter's run.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4, Theorem 79.4, and §3.4.2–3.4.3, Theorem 87.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 and §3.3.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

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
  simp only [NUPPT.advInput_eq, List.length_ofFn] at h1 h2 ⊢
  rw [h1, h2, ofFn_snoc_eq]

/-- The pre-processing of the predictor of [PS10, Theorem 79.4]: on the view
`⟨⟨⟨1^n, y⟩, [σ]⟩, [flip]⟩` form the distinguisher's input `y ++ [σ]`. -/
def owpPredPre (w : List Bool) : List Bool := NUPPT.inArg w ++ NUPPT.inAdvice w

/-- The defining equation of `owpPredPre`: `owpPredPre w = NUPPT.inArg w ++ NUPPT.inAdvice w`. -/
theorem owpPredPre_def (w : List Bool) :
    owpPredPre w =
      (NUPPT.inArg w ++ NUPPT.inAdvice w) := rfl

/-- The post-processing of the predictor of [PS10, Theorem 79.4]: on `⟨view, answer⟩` output
`[xor (if answer = [true] then σ else !σ) flip]`. -/
def owpPredPost (v : List Bool) : List Bool :=
  [xor (if pairSndD v = [true] then (NUPPT.inAdvice (pairFstD v)).headD false
    else !(NUPPT.inAdvice (pairFstD v)).headD false) ((NUPPT.inCoins (pairFstD v)).headD false)]

/-- The pre-processing of the predictor is polynomial-time. -/
theorem owpPredPre_poly : PolyTimeComputable owpPredPre :=
  NUPPT.polyTimeComputable_inArg.append NUPPT.polyTimeComputable_inAdvice

/-- The post-processing of the predictor is polynomial-time (`polyTimeComputable_pairEq` for
the verdict test, `polyTimeComputable_headD` for the two bits, `polyTimeComputable_ite`,
`BinArith.polyTimeComputable_xor`).

**Proof sketch.** On `v = ⟨w, out⟩` the verdict bit `[out = [true]]` is `polyTimeComputable_pairEq`
against the constant `[true]`; the advice bit `σ` and the coin bit `flip` are heads of the
advice and coin projections of `w` (`polyTimeComputable_headD`); the selected bit
`if out = [true] then σ else !σ` is `polyTimeComputable_ite` with `polyTimeComputable_not`;
the output is its `xor` with `flip` (`BinArith.polyTimeComputable_xor`). -/
theorem owpPredPost_poly : PolyTimeComputable owpPredPost := by
  have htest : PolyTimeComputable fun v : List Bool => [decide (pairSndD v = [true])] := by
    convert polyTimeComputable_pairEq.comp
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [true])) using 1
    funext v
    simp
  have hσ : PolyTimeComputable fun v : List Bool =>
      [(NUPPT.inAdvice (pairFstD v)).headD false] :=
    polyTimeComputable_headD.comp (NUPPT.polyTimeComputable_inAdvice.comp
        polyTimeComputable_pairFstD)
  have hflip : PolyTimeComputable fun v : List Bool =>
      [(NUPPT.inCoins (pairFstD v)).headD false] :=
    polyTimeComputable_headD.comp (NUPPT.polyTimeComputable_inCoins.comp
        polyTimeComputable_pairFstD)
  have hite : PolyTimeComputable fun v : List Bool =>
      [if pairSndD v = [true] then (NUPPT.inAdvice (pairFstD v)).headD false
        else !(NUPPT.inAdvice (pairFstD v)).headD false] := by
    convert polyTimeComputable_ite htest hσ (polyTimeComputable_not hσ) using 1
    funext v
    by_cases hv : pairSndD v = [true] <;> simp [hv]
  exact BinArith.polyTimeComputable_xor hite hflip

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
  unfold owpPredMachine
  simp only [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq]
  rw [NUPPT.runAt_wrap D owpPredPre_poly owpPredPost_poly (fun n => [flip n]) (.const 1)
    (fun _ => by simp) (.const 1) n (List.ofFn y) (m := 1) rfl (fun _ => σ) c r
    (by rw [hr]; rfl)]
  have h1 : List.ofFn (fun _ : Fin 1 => σ) = [σ] := by simp [List.ofFn_succ]
  simp only [owpPredPost, owpPredPre, pairSndD_pairEncode, pairFstD_pairEncode,
    NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.inCoins_layout, h1, List.headD_cons]
  simp only [← ofFn_snoc_eq, NUPPT.runAt_eq]
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
  have hcoinLen : 1 + D.coinLen n = (owpPredMachine D flip).coinLen n := by
    simp only [NUPPT.coinLen_eq, owpPredMachine, NUPPT.coins_wrap, PolyExpr.eval_add, PolyExpr.eval_const]
  refine predProb_coins_equiv f B _ _
    (((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      ((Fin.appendEquiv 1 (D.coinLen n)).trans (finCastEquiv hcoinLen))) fun y c => ?_
  obtain ⟨σ, c⟩ := c
  refine owpPredMachine_predictor D flip n y σ c _ ?_
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq,
    ofFn_finCastEquiv]
  exact (ofFn_appendEquiv ((Equiv.funUnique (Fin 1) Bool).symm σ) c).trans
    (congrArg (· ++ List.ofFn c) (by simp [List.ofFn_succ]))

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
  simp only [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    take_ofFn_append, drop_ofFn_append]
  rw [← NUPPT.advInput_eq, hFx]

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
  have hcoinLen : 𝓕.inLen.eval n + A.coinLen n = (glPadInvMachine A 𝓕.inLen).coinLen n := by
    simp only [NUPPT.coinLen_eq, glPadInvMachine, NUPPT.coins_wrap, PolyExpr.eval_add]
  simp only [invProbOpt_def]
  refine le_of_eq_of_le (uprob_comp_equiv
    ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).prodCongr (Equiv.refl (A.Coins n))) _).symm ?_
  refine le_of_le_of_eq ?_ ((uprob_comp_equiv
    (Equiv.prodAssoc (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.inLen.eval n) → Bool) (A.Coins n)) _).trans
    (uprob_comp_equiv ((Equiv.refl (Fin (𝓕.inLen.eval n) → Bool)).prodCongr
      ((Fin.appendEquiv (𝓕.inLen.eval n) (A.coinLen n)).trans (finCastEquiv hcoinLen))) _))
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨x, r⟩, c⟩ := w
  obtain ⟨x', hx', hfx'⟩ := hw
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq, Equiv.symm_apply_apply,
    Equiv.prodAssoc_apply, Equiv.trans_apply, NUPPT.inverter_eq_some_iff] at hx' hfx' ⊢
  obtain ⟨⟨x'', r''⟩, rfl⟩ := (Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).surjective x'
  simp only [Equiv.symm_apply_apply] at hfx' hx'
  have hpair := (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).injective
    (show Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n) (x'', r'')) =
      Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n) (x, r)) from hfx')
  simp only [HardcoreBit.glPad_apply, Prod.mk.injEq] at hpair
  refine ⟨x'', ?_, hpair.1⟩
  rw [glPadInvMachine_runAt A 𝓕.inLen n _ r c _ (by rw [ofFn_finCastEquiv, ofFn_appendEquiv])]
  simp only [HardcoreBit.glPad_apply] at hx'
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

/-- The defining equation of `glPadDecode`: decode `w` as a pair `⟨a, b⟩`, then `a` by `F.decD i`
and `b` as an `L`-bit string; `none` if any step fails. -/
theorem glPadDecode_def (F : Collection) (i : List Bool) (L : ℕ) (w : List Bool) :
    glPadDecode F i L w =
      match pairDecode w with
      | some (a, b) => match F.decD i a, decodeFin L b with
        | some x, some r => some (x, r)
        | _, _ => none
      | none => none := rfl

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
  have h1 := (((F.sampleClose_iff δ).1 hclose n r).prod h0).map
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
  have hcoinLen : m.eval n + A.coinLen n = (glPadCollInvMachine A m).coinLen n := by
    simp only [NUPPT.coinLen_eq, glPadCollInvMachine, NUPPT.coins_wrap, PolyExpr.eval_add]
  simp only [Collection.invProbAt_eq]
  refine OneWay.uexp_mono fun r => ?_
  refine le_of_eq_of_le (uprob_comp_equiv
    (((Equiv.refl (F.D (F.index n r))).prodCongr (finCastEquiv (hL r).symm)).prodCongr
        (Equiv.refl (A.Coins n))) _).symm ?_
  refine le_of_le_of_eq ?_ ((uprob_comp_equiv
    (Equiv.prodAssoc (F.D (F.index n r)) (Fin (m.eval n) → Bool) (A.Coins n)) _).trans
    (uprob_comp_equiv ((Equiv.refl (F.D (F.index n r))).prodCongr
      ((Fin.appendEquiv (m.eval n) (A.coinLen n)).trans (finCastEquiv hcoinLen))) _))
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨x, ρ⟩, c⟩ := w
  obtain ⟨⟨x', ρ'⟩, hx', hfx'⟩ := hw
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq, Equiv.prodAssoc_apply,
    Equiv.trans_apply, ofFn_finCastEquiv] at hx' hfx' ⊢
  have hf : F.f (F.index n r) x' = F.f (F.index n r) x := by
    have := congrArg pairDecode hfx'
    simp only [pairDecode_pairEncode, Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  obtain ⟨a, b, hab, ha, -⟩ := glPadDecode_eq_some F (F.index n r) _ hx'
  refine ⟨x', ?_, hf⟩
  rw [glPadCollInvMachine_runAt A m n _ _ ρ c _ (by rw [ofFn_finCastEquiv, ofFn_appendEquiv]),
    hab, pairFstD_pairEncode, ha]

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
  NUPPT.coins_ofPolyTime _ _ _ _ _

/-- The parameter-change machine at `n` behaves as `A` at `p(n)`. -/
theorem runAtL_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) (y r : List Bool) :
    (A.reparam p).runAtL n y r = A.runAtL (p.eval n) y r := by
  unfold reparam
  rw [runAtL_ofPolyTime]
  simp [runAtL_eq, advInput_eq, layout_eq, inParam_eq, inArg_eq, inAdvice_eq, inCoins_eq]

/-- The number of coins of the parameter-change machine at `n` is that of `A` at `p(n)`. -/
theorem coinLen_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) :
    (A.reparam p).coinLen n = A.coinLen (p.eval n) := by
  simp [coinLen_eq, PolyExpr.eval_subst]

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

/-! ## Helpers of the padded families and collections (`Asymptotic/HardCore.lean`,
`Asymptotic/HardCoreCollection.lean`) -/

/-- The re-encoding `(x ‖ r, c) ↦ ((x, r), c)` of the experiments. -/
def splitPair (a b : ℕ) (ρ : Type*) :
    (Fin (a + b) → Bool) × ρ ≃ ((Fin a → Bool) × (Fin b → Bool)) × ρ where
  toFun z := ((Fin.appendEquiv a b).symm z.1, z.2)
  invFun z := (Fin.appendEquiv a b z.1, z.2)
  left_inv z := Prod.ext ((Fin.appendEquiv a b).apply_symm_apply z.1) rfl
  right_inv z := Prod.ext ((Fin.appendEquiv a b).symm_apply_apply z.1) rfl

/-- The forward map of `splitPair`: `splitPair a b ρ z = ((Fin.appendEquiv a b).symm z.1, z.2)`. -/
theorem splitPair_apply (a b : ℕ) (ρ : Type*) (z : (Fin (a + b) → Bool) × ρ) :
    splitPair a b ρ z = ((Fin.appendEquiv a b).symm z.1, z.2) := rfl

/-- The inverse of `splitPair`: `(splitPair a b ρ).symm z = (Fin.appendEquiv a b z.1, z.2)`. -/
theorem splitPair_symm_apply (a b : ℕ) (ρ : Type*) (z : ((Fin a → Bool) × (Fin b → Bool)) × ρ) :
    (splitPair a b ρ).symm z = (Fin.appendEquiv a b z.1, z.2) := rfl

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

/-- The defining equation of `glPadSampleFun` (its body, unfolded once). -/
theorem glPadSampleFun_def (z : List Bool) :
    glPadSampleFun F z =
      (pairEncode
        (F.sample.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) []
          ((pairSndD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).take
            (F.sample.coins.eval
                (pairFstD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).length))))
        ((pairSndD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).drop
          (F.sample.coins.eval
              (pairFstD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).length))) := rfl

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
  simp only [NUPPT.runAt_eq, NUPPT.output_ofPolyTimeUniform,
    glPadSampleFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, NUPPT.layout_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform.advice_eq n,
    NUPPT.coinLen_eq, NUPPT.runAtL_eq]

end Collection

/-- The raw trapdoor inverter of the padded collection on the layout
`⟨⟨⟨1^n, ⟨t, ⟨y, r⟩⟩⟩, []⟩, s⟩`: run `Inv(1^n, ⟨t, y⟩; s)` and append `r`. -/
def glPadInvFun (T : TrapdoorCollection) (z : List Bool) : List Bool :=
  pairEncode
    (T.inv.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))) []
      (NUPPT.inCoins z)))
    (pairSndD (pairSndD (NUPPT.inArg z)))

/-- `glPadInvFun T z = ⟨Inv(1^n, ⟨t, y⟩; s), r⟩` on `z = ⟨⟨⟨1^n, ⟨t, ⟨y, r⟩⟩⟩, []⟩, s⟩`. -/
theorem glPadInvFun_eq (T : TrapdoorCollection) (z : List Bool) : glPadInvFun T z = pairEncode
    (T.inv.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))) []
      (NUPPT.inCoins z))) (pairSndD (pairSndD (NUPPT.inArg z))) := rfl

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
