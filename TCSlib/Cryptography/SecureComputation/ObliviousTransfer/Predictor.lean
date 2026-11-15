/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the view-building distinguisher behind Bob's side

On Bob's side of [PS10, Proposition 161.5] a distinguisher `D` of Bob's real and simulated views
becomes a predictor of the enhanced hard-core bit `h(f_i⁻¹(y_{1−b}))` from `⟨i, s'⟩`, `s'` the
sampler coins of `y_{1−b}`. The predictor is the machine `tdpPredictor D' flip` of Algorithm
104.3's proof, run on the distinguisher `D'` built here: on `⟨i, ⟨s', [β]⟩⟩` with its own coins
`s₁ ++ ρ`, `D'` assembles Bob's view with tape `s₁ ++ s'`, index `i`, the selected mask
`z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ a_b` and the unselected mask `z_{1−b} = β ⊕ a_{1−b}` (`OT.bobView`),
and runs `D` on it with the coins `ρ`. The choice and sender bits `(b, a₀, a₁)` are fixed in the
machine.

## Main definitions

* `OT.bobView`: Bob's view (paired with Alice's empty output) with a given unselected mask bit.
* `OT.viewRaw`, `OT.viewDistRaw`: the raw functions of the view and of `D'`.
* `OT.viewDist`: the machine `D'`; `OT.viewDistCoins`: its coins as `Coins_Sample × Coins_D`.

## Main results

* `OT.polyTimeComputable_bobView`, `OT.polyTimeComputable_viewDistRaw`: they are
  polynomial-time.
* `OT.distinguisherL_viewDist`: `D'` accepts `⟨i, ⟨s', [β]⟩⟩` on `(s₁, ρ)` iff `D` accepts the
  view `bobView … β` on `ρ`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5, and Theorem 104.4 (the predictor), book pp. 104, 161–162.
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-- **Bob's view with the unselected mask bit `β`** [PS10, Proposition 161.5], paired with
Alice's empty output: `⟨⟨⟨u, [b]⟩, ⟨s, [i, Z, []]⟩⟩, []⟩` with
`Z = ⟨[β ⊕ a₀], H ⟨i, w⟩ ⊕ [a₁]⟩` if `b`, else `⟨H ⟨i, w⟩ ⊕ [a₀], [β ⊕ a₁]⟩`. -/
def bobView (u : List Bool) (b a₀ a₁ : Bool) (i s w : List Bool) (β : Bool) : List Bool :=
  pairEncode (pairEncode (pairEncode u [b]) (pairEncode s (pairEncode i (pairEncode
    (if b then pairEncode [xor β a₀] (List.zipWith xor (H (pairEncode i w)) [a₁])
      else pairEncode (List.zipWith xor (H (pairEncode i w)) [a₀]) [xor β a₁])
    (pairEncode [] []))))) []

/-- The defining equation of `bobView`: `bobView H u b a₀ a₁ i s w β =
⟨⟨⟨u, [b]⟩, ⟨s, [i, Z, []]⟩⟩, []⟩` with `Z` ordered by `b`. -/
theorem bobView_eq (u : List Bool) (b a₀ a₁ : Bool) (i s w : List Bool) (β : Bool) :
    bobView H u b a₀ a₁ i s w β =
      pairEncode (pairEncode (pairEncode u [b]) (pairEncode s (pairEncode i (pairEncode
        (if b then pairEncode [xor β a₀] (List.zipWith xor (H (pairEncode i w)) [a₁])
          else pairEncode (List.zipWith xor (H (pairEncode i w)) [a₀]) [xor β a₁])
        (pairEncode [] []))))) [] := rfl

/-- **Bob's view is polynomial-time** in its string arguments, for polynomial-time `H`
(pairing, one XOR of bits `BinArith.polyTimeComputable_xor`, `polyTimeComputable_pairXor`, a
branch on the fixed bit `b`): `PolyTimeComputable (fun z =>
bobView H (U z) b a₀ a₁ (I z) (S z) (W z) ((B z).headD false))`. -/
theorem polyTimeComputable_bobView {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (b a₀ a₁ : Bool) {U I S W B : List Bool → List Bool} (hU : PolyTimeComputable U)
    (hI : PolyTimeComputable I) (hS : PolyTimeComputable S) (hW : PolyTimeComputable W)
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => bobView H (U z) b a₀ a₁ (I z) (S z) (W z) ((B z).headD false) := by
  have hβ := polyTimeComputable_headD.comp' hB
  have hx : ∀ a : Bool, PolyTimeComputable fun z => [xor ((B z).headD false) a] := fun a =>
    BinArith.polyTimeComputable_xor hβ (polyTimeComputable_const [a])
  have hm : ∀ a : Bool, PolyTimeComputable fun z =>
      List.zipWith xor (H (pairEncode (I z) (W z))) [a] := fun a =>
    (polyTimeComputable_pairXor.comp' ((hH.comp' (hI.pairEncode hW)).pairEncode
      (polyTimeComputable_const [a]))).congr fun z => by
        rw [pairFstD_pairEncode, pairSndD_pairEncode]
  have hZ := polyTimeComputable_ite (p := fun _ => b) (polyTimeComputable_const [b])
    ((hx a₀).pairEncode (hm a₁)) ((hm a₀).pairEncode (hx a₁))
  have h := ((hU.pairEncode (polyTimeComputable_const [b])).pairEncode (hS.pairEncode
    (hI.pairEncode (hZ.pairEncode (polyTimeComputable_const (pairEncode [] [])))))).pairEncode
    (polyTimeComputable_const [])
  exact h.congr fun z => (bobView_eq H _ _ _ _ _ _ _ _).symm

/-- The view built by `D'` on the raw layout `z = layout u ⟨i, ⟨s', [β]⟩⟩ α (s₁ ++ ρ)`:
`bobView u b a₀ a₁ i (s₁ ++ s') (Sample(u, i; s₁)) β`, with `s₁` the first `coins_Sample(|u|)`
coins. -/
def viewRaw (b a₀ a₁ : Bool) (z : List Bool) : List Bool :=
  bobView H (NUPPT.inParam z) b a₀ a₁ (pairFstD (NUPPT.inArg z))
    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length) ++
      pairFstD (pairSndD (NUPPT.inArg z)))
    (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
      ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))))
    ((pairSndD (pairSndD (NUPPT.inArg z))).headD false)

/-- The defining equation of `viewRaw`: `viewRaw T H b a₀ a₁ z = bobView H u b a₀ a₁ i
(s₁ ++ s') (Sample(u, i; s₁)) β` read off the layout `z`. -/
theorem viewRaw_eq (b a₀ a₁ : Bool) (z : List Bool) :
    viewRaw T H b a₀ a₁ z =
      bobView H (NUPPT.inParam z) b a₀ a₁ (pairFstD (NUPPT.inArg z))
        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length) ++
          pairFstD (pairSndD (NUPPT.inArg z)))
        (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
          ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))))
        ((pairSndD (pairSndD (NUPPT.inArg z))).headD false) := rfl

/-- The raw function of `D'`: `D` on the layout of `1^n`, the built view, the advice and the
coins after the first `coins_Sample(n)`: `viewDistRaw T H D b a₀ a₁ z = D.output (layout
(inParam z) (viewRaw T H b a₀ a₁ z) (inAdvice z) ((inCoins z).drop coins_Sample(n)))`. -/
def viewDistRaw (D : NUPPT) (b a₀ a₁ : Bool) (z : List Bool) : List Bool :=
  D.output (NUPPT.layout (NUPPT.inParam z) (viewRaw T H b a₀ a₁ z) (NUPPT.inAdvice z)
    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `viewDistRaw`: `viewDistRaw T H D b a₀ a₁ z = D.output (layout
(inParam z) (viewRaw T H b a₀ a₁ z) (inAdvice z) ((inCoins z).drop coins_Sample(n)))`. -/
theorem viewDistRaw_eq (D : NUPPT) (b a₀ a₁ : Bool) (z : List Bool) :
    viewDistRaw T H D b a₀ a₁ z =
      D.output (NUPPT.layout (NUPPT.inParam z) (viewRaw T H b a₀ a₁ z) (NUPPT.inAdvice z)
        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- **The raw function of `D'` is polynomial-time** (`polyTimeComputable_bobView`, the sampler's
and `D`'s output functions, `polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`,
`PolyTimeComputable.append`): `PolyTimeComputable (viewDistRaw T H D b a₀ a₁)`.

**Proof sketch.** Build the projections, the first coin block and the remaining coins, the sampled
element on the first block, the tape `s₁ ++ s'` and the built view (`polyTimeComputable_bobView`),
then `D`'s output on the layout; match the definition by the pairing readers. -/
theorem polyTimeComputable_viewDistRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (D : NUPPT) (b a₀ a₁ : Bool) : PolyTimeComputable (viewDistRaw T H D b a₀ a₁) := by
  have hU := NUPPT.polyTimeComputable_inParam
  have hi := polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg
  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hs := htake.append (polyTimeComputable_pairFstD.comp'
    (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg))
  have hw := T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
    (polyTimeComputable_const []) htake)
  have hβ := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg)
  have hv := polyTimeComputable_bobView hH b a₀ a₁ hU hi hs hw hβ
  have h := D.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hv
    NUPPT.polyTimeComputable_inAdvice hdrop)
  refine h.congr fun z => ?_
  simp only [viewDistRaw_eq, viewRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The view-building distinguisher `D'`** for the fixed bits `(b, a₀, a₁)`: `D`'s advice and
coins `coins_Sample + coins_D`: `viewDist T hH D b a₀ a₁ = NUPPT.ofPolyTime
(polyTimeComputable_viewDistRaw T hH D b a₀ a₁) (.add T.sample.coins D.coins) D.adv D.advice
D.advice_length`. -/
noncomputable def viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_viewDistRaw T hH D b a₀ a₁) (.add T.sample.coins D.coins)
    D.adv D.advice D.advice_length

/-- The coin polynomial of `D'` is `coins_Sample + coins_D`:
`(viewDist T hH D b a₀ a₁).coins = .add T.sample.coins D.coins`. -/
theorem viewDist_coins {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) : (viewDist T hH D b a₀ a₁).coins = .add T.sample.coins D.coins :=
  NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **`D'`'s coins** as a sampler block and `D`'s coins:
`(viewDist T hH D b a₀ a₁).Coins n ≃ T.sample.Coins n × D.Coins n` (`splitLen`). -/
noncomputable def viewDistCoins {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) (n : ℕ) : (viewDist T hH D b a₀ a₁).Coins n ≃ T.sample.Coins n × D.Coins n :=
  splitLen (by rw [NUPPT.coinLen_eq, viewDist_coins, PolyExpr.eval_add, NUPPT.coinLen_eq,
    NUPPT.coinLen_eq])

/-- The tape of `D'` from blocks: `ofFn ((viewDistCoins …).symm (s₁, ρ)) = ofFn s₁ ++ ofFn ρ`. -/
theorem viewDistCoins_symm_ofFn {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (D : NUPPT) (b a₀ a₁ : Bool) (n : ℕ) (p : T.sample.Coins n × D.Coins n) :
    List.ofFn ((viewDistCoins T hH D b a₀ a₁ n).symm p) = List.ofFn p.1 ++ List.ofFn p.2 :=
  splitLen_symm_ofFn _ p

/-- **`D'` runs `D` on the built view**: on `⟨i, ⟨s', [β]⟩⟩` with coins `s₁ ++ ρ`,
`D'(1^n, ⟨i, ⟨s', [β]⟩⟩; s₁ ++ ρ) = D(1^n, bobView (1^n) b a₀ a₁ i (s₁ ++ s') w β; ρ)` with
`w = Sample(1^n, i; s₁)`. -/
theorem runAtL_viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H) (D : NUPPT)
    (b a₀ a₁ : Bool) (n : ℕ) (i s' : List Bool) (β : Bool) (s₁ : T.sample.Coins n)
    (ρ : List Bool) :
    (viewDist T hH D b a₀ a₁).runAtL n (pairEncode i (pairEncode s' [β])) (List.ofFn s₁ ++ ρ) =
      D.runAtL n (bobView H (List.replicate n true) b a₀ a₁ i (List.ofFn s₁ ++ s')
        (T.sample.runAt n i s₁) β) ρ := by
  have hl : (List.ofFn s₁).length = T.sample.coins.eval (List.replicate n true).length := by
    rw [length_ofFn_coins, List.length_replicate]
  unfold viewDist
  rw [NUPPT.runAtL_ofPolyTime, NUPPT.advInput_eq, ← NUPPT.layout_eq, viewDistRaw_eq, viewRaw_eq,
    NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.inCoins_layout,
    List.take_left' hl, List.drop_left' hl, pairFstD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, NUPPT.runAtL_eq_output_layout,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]

/-- **`D'` accepts iff `D` accepts the built view**: `D'.distinguisherL n ⟨i, ⟨s', [β]⟩⟩ (s₁, ρ) =
D.distinguisherL n (bobView (1^n) b a₀ a₁ i (s₁ ++ s') (Sample(1^n, i; s₁)) β) ρ`. -/
theorem distinguisherL_viewDist {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (D : NUPPT) (b a₀ a₁ : Bool) (n : ℕ) (i s' : List Bool) (β : Bool)
    (p : T.sample.Coins n × D.Coins n) :
    (viewDist T hH D b a₀ a₁).distinguisherL n (pairEncode i (pairEncode s' [β]))
        ((viewDistCoins T hH D b a₀ a₁ n).symm p) =
      D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ i (List.ofFn p.1 ++ s')
        (T.sample.runAt n i p.1) β) p.2 := by
  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq,
    viewDistCoins_symm_ofFn, runAtL_viewDist]

end TCSlib.Cryptography.SecureComputation.OT
