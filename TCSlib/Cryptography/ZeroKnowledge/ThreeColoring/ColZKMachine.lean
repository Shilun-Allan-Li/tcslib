/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorMachine
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hiding reduction of the 3-colouring simulator as a machine

The machine behind step (4) of `col_zk`'s proof sketch (`ThreeColoring/Simulator.lean`): the
hiding reduction of [PS10, proof of Proposition 128.8] with its attempt table fixed (gate 03g
review §2.1) reads only one attempt's challenge, so it is the string function `hidingView` of
the hard-wired data and the challenge commitment vector, followed by one call of the
distinguisher. This file defines `hidingView`, proves it polynomial-time (one call of the
verifier's uniform machine, `polyTimeComputable_next`), packages the reduction as an `NUPPT`
at parameter `n` calling `D` at parameter `n²` (`exists_colHidingRed`), and transports its
coins (`distAdv_distinguisherL_reparam`).

## Main definitions

* `TCSlib.Cryptography.ColZK.hidingView` — the view handed to `D` by the fixed hiding
  reduction, as a function of its advice and the challenge.
* `TCSlib.Cryptography.ColZK.edgelessAdv`, `TCSlib.Cryptography.ColZK.plantedAdv` — the advice
  of the edgeless and of the planted case.

## Main results

* `TCSlib.Cryptography.ColZK.hidingView_edgelessAdv`, `hidingView_plantedAdv_some`,
  `hidingView_plantedAdv_none` — `hidingView` on its two kinds of advice.
* `TCSlib.Cryptography.ColZK.polyTimeComputable_next` — one activation of an efficient
  strategy is polynomial-time.
* `TCSlib.Cryptography.ColZK.polyTimeComputable_hidingView` — `hidingView` is polynomial-time.
* `TCSlib.Cryptography.ColZK.exists_colHidingRed` — the fixed hiding reduction is an `NUPPT`.
* `TCSlib.Cryptography.ColZK.distAdv_distinguisherL_reparam` — the two-parameter coin
  transport (requested shared lemma).
* `TCSlib.Cryptography.ColZK.exists_hidingView_bound` — the hiding bound for all the fixed
  reductions at once (the worst data at each `n`, `Commitment.multiHiding`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Proposition 128.8 and its proof, p. 129.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColZK

open Complexity Turing

/-! ### The view of the fixed hiding reduction -/

/-- The view handed to the distinguisher by the fixed hiding reduction of [PS10, proof of
Proposition 128.8] on the advice `adv` (an encoded list of fields, field `i` being
`pairFstD (pairSndD^[i] adv)`) and the challenge `cv`. Fields `0, 1, 2` are `x`, `z` and the
verifier's tape `ρ`. If field `3` is empty (the edgeless case) the view is `⟨x, z, ρ, [cv, []]⟩`.
Otherwise, if field `4` is nonempty the view is field `14` (a success before the planted
attempt); else the planted commitment message is the message list of field `5`'s length `n`
whose entries at the positions `|field 6|`, `|field 7|` are fields `8`, `9` and whose other
entries are those of `cv`, the verifier is called once on it with tape `ρ`, and the view is
`⟨x, z, ρ, [com, field 12]⟩` if the reply names the edge `|field 11|` modulo `|field 10|`,
field `13` (the later attempts' outcome) otherwise. -/
def hidingView (V' : Strategy) (adv cv : List Bool) : List Bool :=
  if pairFstD (pairSndD^[3] adv) = [] then
    View.encode ⟨pairFstD adv, pairFstD (pairSndD^[1] adv), pairFstD (pairSndD^[2] adv), [cv, []]⟩
  else if pairFstD (pairSndD^[4] adv) = [] then
    if (V'.next (pairFstD adv) (pairFstD (pairSndD^[1] adv)) (pairFstD (pairSndD^[2] adv))
        [(List.range (pairFstD (pairSndD^[5] adv)).length).flatMap fun i =>
          pairEncode (if i = (pairFstD (pairSndD^[6] adv)).length then pairFstD (pairSndD^[8] adv)
            else if i = (pairFstD (pairSndD^[7] adv)).length then pairFstD (pairSndD^[9] adv)
            else pairFstD (pairSndD^[i] cv)) []]).length %
          (pairFstD (pairSndD^[10] adv)).length = (pairFstD (pairSndD^[11] adv)).length then
      View.encode ⟨pairFstD adv, pairFstD (pairSndD^[1] adv), pairFstD (pairSndD^[2] adv),
        [(List.range (pairFstD (pairSndD^[5] adv)).length).flatMap fun i =>
          pairEncode (if i = (pairFstD (pairSndD^[6] adv)).length then pairFstD (pairSndD^[8] adv)
            else if i = (pairFstD (pairSndD^[7] adv)).length then pairFstD (pairSndD^[9] adv)
            else pairFstD (pairSndD^[i] cv)) [],
          pairFstD (pairSndD^[12] adv)]⟩
    else pairFstD (pairSndD^[13] adv)
  else pairFstD (pairSndD^[14] adv)

/-- The defining equation of `hidingView` (its docstring's formula).

**Proof sketch.** By definition (`rfl`). -/
theorem hidingView_eq (V' : Strategy) (adv cv : List Bool) :
    hidingView V' adv cv =
      if pairFstD (pairSndD^[3] adv) = [] then
        View.encode ⟨pairFstD adv, pairFstD (pairSndD^[1] adv), pairFstD (pairSndD^[2] adv),
          [cv, []]⟩
      else if pairFstD (pairSndD^[4] adv) = [] then
        if (V'.next (pairFstD adv) (pairFstD (pairSndD^[1] adv)) (pairFstD (pairSndD^[2] adv))
            [(List.range (pairFstD (pairSndD^[5] adv)).length).flatMap fun i =>
              pairEncode (if i = (pairFstD (pairSndD^[6] adv)).length then
                pairFstD (pairSndD^[8] adv)
                else if i = (pairFstD (pairSndD^[7] adv)).length then pairFstD (pairSndD^[9] adv)
                else pairFstD (pairSndD^[i] cv)) []]).length %
              (pairFstD (pairSndD^[10] adv)).length = (pairFstD (pairSndD^[11] adv)).length then
          View.encode ⟨pairFstD adv, pairFstD (pairSndD^[1] adv), pairFstD (pairSndD^[2] adv),
            [(List.range (pairFstD (pairSndD^[5] adv)).length).flatMap fun i =>
              pairEncode (if i = (pairFstD (pairSndD^[6] adv)).length then
                pairFstD (pairSndD^[8] adv)
                else if i = (pairFstD (pairSndD^[7] adv)).length then pairFstD (pairSndD^[9] adv)
                else pairFstD (pairSndD^[i] cv)) [],
              pairFstD (pairSndD^[12] adv)]⟩
        else pairFstD (pairSndD^[13] adv)
      else pairFstD (pairSndD^[14] adv) := rfl

/-- The advice of the edgeless case: `x`, `z`, the verifier's tape `ρ` and the empty mode
field. -/
def edgelessAdv (x z ρ : List Bool) : List Bool := Strategy.encodeMsgs [x, z, ρ, []]

/-- The defining equation of `edgelessAdv`: `encodeMsgs [x, z, ρ, []]`. -/
theorem edgelessAdv_eq (x z ρ : List Bool) :
    edgelessAdv x z ρ = Strategy.encodeMsgs [x, z, ρ, []] := rfl

/-- The advice of the planted case: `x`, `z`, the planted attempt's verifier tape `ρ`, the
vertex count `n`, the endpoints `p₁, p₂` with their commitments `A₁, A₂`, the edge count `m`, the
planted edge index `e₀`, the planted opening `opn`, the encoded outcome `post` of the later
attempts, and the encoded outcome `pre` of the earlier attempts if one of them succeeded. -/
def plantedAdv (x z ρ : List Bool) (n p₁ p₂ : ℕ) (A₁ A₂ : List Bool) (m e₀ : ℕ)
    (opn post : List Bool) (pre : Option (List Bool)) : List Bool :=
  Strategy.encodeMsgs [x, z, ρ, [true], if pre.isSome then [true] else [],
    List.replicate n true, List.replicate p₁ true, List.replicate p₂ true, A₁, A₂,
    List.replicate m true, List.replicate e₀ true, opn, post, pre.getD []]

/-- The defining equation of `plantedAdv` (its docstring's field list). -/
theorem plantedAdv_eq (x z ρ : List Bool) (n p₁ p₂ : ℕ) (A₁ A₂ : List Bool) (m e₀ : ℕ)
    (opn post : List Bool) (pre : Option (List Bool)) :
    plantedAdv x z ρ n p₁ p₂ A₁ A₂ m e₀ opn post pre =
      Strategy.encodeMsgs [x, z, ρ, [true], if pre.isSome then [true] else [],
        List.replicate n true, List.replicate p₁ true, List.replicate p₂ true, A₁, A₂,
        List.replicate m true, List.replicate e₀ true, opn, post, pre.getD []] := rfl

/-- Field `i` of an encoded list is its entry `i` (`ColMachines.getD_eq_pairFstD_iterate`). -/
theorem field_encodeMsgs (l : List (List Bool)) (i : ℕ) :
    pairFstD (pairSndD^[i] (Strategy.encodeMsgs l)) = l.getD i [] :=
  (ColMachines.getD_eq_pairFstD_iterate l i).symm

/-- Field `0` of an encoded list is its entry `0`. -/
theorem field_zero_encodeMsgs (l : List (List Bool)) :
    pairFstD (Strategy.encodeMsgs l) = l.getD 0 [] :=
  field_encodeMsgs l 0

/-- **The edgeless view**: on `edgelessAdv x z ρ` the view is `⟨x, z, ρ, [cv, []]⟩`. -/
theorem hidingView_edgelessAdv (V' : Strategy) (x z ρ cv : List Bool) :
    hidingView V' (edgelessAdv x z ρ) cv = View.encode ⟨x, z, ρ, [cv, []]⟩ := by
  rw [hidingView_eq, edgelessAdv_eq]
  simp only [field_encodeMsgs, field_zero_encodeMsgs, List.getD_cons_succ, List.getD_cons_zero,
    if_true]

/-- **A success before the planted attempt**: on `plantedAdv … (some v)` the view is `v`. -/
theorem hidingView_plantedAdv_some (V' : Strategy) (x z ρ : List Bool) (n p₁ p₂ : ℕ)
    (A₁ A₂ : List Bool) (m e₀ : ℕ) (opn post v cv : List Bool) :
    hidingView V' (plantedAdv x z ρ n p₁ p₂ A₁ A₂ m e₀ opn post (some v)) cv = v := by
  rw [hidingView_eq, plantedAdv_eq]
  simp only [field_encodeMsgs, field_zero_encodeMsgs, List.getD_cons_succ, List.getD_cons_zero,
    Option.isSome_some, if_true, Option.getD_some, if_neg (List.cons_ne_nil _ _)]

/-- **The planted attempt**: on `plantedAdv … none` the view is `⟨x, z, ρ, [com, opn]⟩` if the
verifier's reply to the spliced commitment message `com` (entries `A₁`, `A₂` at `p₁`, `p₂`, the
challenge's entries elsewhere) names `e₀` modulo `m`, and `post` otherwise. -/
theorem hidingView_plantedAdv_none (V' : Strategy) (x z ρ : List Bool) (n p₁ p₂ : ℕ)
    (A₁ A₂ : List Bool) (m e₀ : ℕ) (opn post cv : List Bool) :
    hidingView V' (plantedAdv x z ρ n p₁ p₂ A₁ A₂ m e₀ opn post none) cv =
      let com := Strategy.encodeMsgs (List.ofFn fun i : Fin n =>
        if (i : ℕ) = p₁ then A₁ else if (i : ℕ) = p₂ then A₂ else pairFstD (pairSndD^[i] cv))
      if (V'.next x z ρ [com]).length % m = e₀ then View.encode ⟨x, z, ρ, [com, opn]⟩
      else post := by
  rw [hidingView_eq, plantedAdv_eq]
  simp only [field_encodeMsgs, field_zero_encodeMsgs, List.getD_cons_succ, List.getD_cons_zero,
    Option.isSome_none, Bool.false_eq_true, if_false, if_true, if_neg (List.cons_ne_nil _ _)]
  have hcom : ((List.range (List.replicate n true).length).flatMap fun i =>
      pairEncode (if i = (List.replicate p₁ true).length then A₁
        else if i = (List.replicate p₂ true).length then A₂ else pairFstD (pairSndD^[i] cv)) []) =
      Strategy.encodeMsgs (List.ofFn fun i : Fin n =>
        if (i : ℕ) = p₁ then A₁ else if (i : ℕ) = p₂ then A₂ else pairFstD (pairSndD^[i] cv)) := by
    rw [ColMachines.encodeMsgs_ofFn_eq_flatMap _ (fun i => if i = p₁ then A₁ else if i = p₂ then A₂
      else pairFstD (pairSndD^[i] cv)) fun _ _ => rfl, List.length_replicate, List.length_replicate,
      List.length_replicate]
  rw [hcom, List.length_replicate, List.length_replicate]

/-! ### Polynomial time -/

/-- **One activation of an efficient strategy is polynomial-time**: for an efficient `V'` and
polynomial-time `X, Z, R, C`, the reply `V'.next (X w) (Z w) (R w) [C w]` is polynomial-time
(`Strategy.efficient_iff`, `Strategy.ofNUPPT_next`, `NUPPT.runAtL_eq_output_layout` and the
machine's `polyTimeComputable_output`; the generic form of `ColSimMachine.reply_poly`, whose
tape is a block of the simulator's layout). -/
theorem polyTimeComputable_next {V' : Strategy} (hV' : V'.Efficient)
    {X Z R C : List Bool → List Bool} (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hR : PolyTimeComputable R) (hC : PolyTimeComputable C) :
    PolyTimeComputable fun w => V'.next (X w) (Z w) (R w) [C w] := by
  obtain ⟨A, hA, -, hnext⟩ := (Strategy.efficient_iff V').1 hV'
  have hlay := NUPPT.polyTimeComputable_layout (polyTimeComputable_unary.comp hX)
    ((hX.pairEncode hZ).pairEncode (hC.pairEncode (polyTimeComputable_const [])))
    (polyTimeComputable_const []) hR
  refine ColSimMachine.ptc_congr (A.polyTimeComputable_output.comp hlay) fun w => ?_
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq,
    Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil]
  rfl

/-- Field `i` of a polynomial-time word is polynomial-time, for a constant `i`. -/
private theorem colZK_field_poly {W : List Bool → List Bool} (hW : PolyTimeComputable W) (i : ℕ) :
    PolyTimeComputable fun w => pairFstD (pairSndD^[i] (W w)) :=
  polyTimeComputable_pairFstD.comp (ColMachines.iterSnd_poly hW (EncodingMachines.unaryConst_poly i))

/-- **`hidingView` is polynomial-time** in its advice and challenge.

**Proof sketch.** The fields are constant-index projections (`ColMachines.iterSnd_poly`); the
spliced commitment message is the concatenation loop `ColMachines.polyTimeComputable_flatMap_range`
over `i < |field 5|` with the entry chosen by two unary comparisons (`eqTest_poly`) and the
challenge's entry `pairFstD (pairSndD^[i] cv)` (`iterSnd_poly` at the unary index); the
verifier's reply is `polyTimeComputable_next`; the test is `modNum_poly`, `eqTest_poly`; the
views are pairings; the three cases are `polyTimeComputable_ite` on `isNil_poly`. -/
theorem polyTimeComputable_hidingView {V' : Strategy} (hV' : V'.Efficient)
    {ADV CV : List Bool → List Bool} (hA : PolyTimeComputable ADV) (hC : PolyTimeComputable CV) :
    PolyTimeComputable fun w => hidingView V' (ADV w) (CV w) := by
  have hf := colZK_field_poly hA
  have hx : PolyTimeComputable fun w => pairFstD (ADV w) := polyTimeComputable_pairFstD.comp hA
  -- the chunk of the splice loop, on `⟨1^i, w⟩`
  have hchunk : PolyTimeComputable fun u =>
      pairEncode (if (pairFstD u).length = (pairFstD (pairSndD^[6] (ADV (pairSndD u)))).length then
          pairFstD (pairSndD^[8] (ADV (pairSndD u)))
        else if (pairFstD u).length = (pairFstD (pairSndD^[7] (ADV (pairSndD u)))).length then
          pairFstD (pairSndD^[9] (ADV (pairSndD u)))
        else pairFstD (pairSndD^[(pairFstD u).length] (CV (pairSndD u)))) [] := by
    have hi := EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD
    have hA' := hA.comp polyTimeComputable_pairSndD
    have h := polyTimeComputable_ite (EncodingMachines.eqTest_poly hi
        (EncodingMachines.unaryLength_poly (colZK_field_poly hA' 6))) (colZK_field_poly hA' 8)
      (polyTimeComputable_ite (EncodingMachines.eqTest_poly hi
        (EncodingMachines.unaryLength_poly (colZK_field_poly hA' 7))) (colZK_field_poly hA' 9)
        (polyTimeComputable_pairFstD.comp
          (ColMachines.iterSnd_poly (hC.comp polyTimeComputable_pairSndD) hi)))
    refine ColSimMachine.ptc_congr (h.pairEncode (polyTimeComputable_const [])) fun u => ?_
    simp only [Function.comp_apply, decide_eq_true_eq]
  have hcom := ColMachines.polyTimeComputable_flatMap_range
    (E := fun w i => pairEncode (if i = (pairFstD (pairSndD^[6] (ADV w))).length then
        pairFstD (pairSndD^[8] (ADV w))
      else if i = (pairFstD (pairSndD^[7] (ADV w))).length then pairFstD (pairSndD^[9] (ADV w))
      else pairFstD (pairSndD^[i] (CV w))) []) hchunk
    (EncodingMachines.unaryLength_poly (hf 5))
  have hrep := polyTimeComputable_next hV' hx (hf 1) (hf 2) hcom
  have htest := EncodingMachines.eqTest_poly (EncodingMachines.modNum_poly
    (EncodingMachines.unaryLength_poly hrep) (EncodingMachines.unaryLength_poly (hf 10)))
    (EncodingMachines.unaryLength_poly (hf 11))
  have hview := ColSimMachine.view_poly hx (hf 1) (hf 2) hcom (hf 12)
  have hview0 := ColSimMachine.view_poly hx (hf 1) (hf 2) hC (polyTimeComputable_const [])
  have h := polyTimeComputable_ite (StateLoop.isNil_poly.comp (hf 3)) hview0
    (polyTimeComputable_ite (StateLoop.isNil_poly.comp (hf 4))
      (polyTimeComputable_ite htest hview (hf 13)) (hf 14))
  refine ColSimMachine.ptc_congr h fun w => ?_
  simp only [decide_eq_true_eq, EncodingMachines.modNum_eq]
  rfl

/-! ### The machine and its coins -/

/-- **The fixed hiding reduction is an `NUPPT`** [PS10, proof of Proposition 128.8, the reduction
to the hiding property] (step (4) of `col_zk`'s sketch, gate 03g review §2.1, item 4): for an
efficient `V'`, a distinguisher `D` and polynomially bounded advice `α`, some `NUPPT` `B` with
`D`'s coins at parameter `n²` runs, at parameter `n` on the challenge `cv`, as `D` at parameter
`n²` on `hidingView V' (α n) cv`.

**Proof sketch.** `NUPPT.exists_comp` with `pre := ⟨cv, adv⟩ ↦ hidingView V' adv cv`
(`polyTimeComputable_hidingView`), then `NUPPT.exists_reparam (.mul .var .var)`, then
`NUPPT.exists_withAdvice α` (the shape of pre-ship probe R4); the run equations compose
(`PolyExpr.eval_mul`, `PolyExpr.eval_var`). -/
theorem exists_colHidingRed {V' : Strategy} (hV' : V'.Efficient) (D : NUPPT) (α : ℕ → List Bool)
    (b : PolyExpr) (hα : ∀ n, (α n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins.subst (.mul .var .var) ∧
      ∀ n cv r, B.runAtL n cv r = D.runAtL (n * n) (hidingView V' (α n) cv) r := by
  obtain ⟨A₁, hc₁, -, -, h₁⟩ := D.exists_comp
    (polyTimeComputable_hidingView hV' polyTimeComputable_pairSndD polyTimeComputable_pairFstD)
    polyTimeComputable_id
  obtain ⟨A₂, hc₂, -, h₂⟩ := A₁.exists_reparam (.mul .var .var)
  obtain ⟨B, hc, h⟩ := A₂.exists_withAdvice α b hα
  refine ⟨B, by rw [hc, hc₂, hc₁], fun n cv r => ?_⟩
  rw [h, h₂, h₁, PolyExpr.eval_mul, PolyExpr.eval_var, pairFstD_pairEncode, pairSndD_pairEncode]
  rfl

/-- **Two-parameter coin transport** (requested shared lemma, gate 03g review #2 ripple): if `B`
has `D`'s coins at parameter `n²` and runs at parameter `n` on `y` as `D` at `n²` on `F y`, then
`B`'s advantage between any two samplers at parameter `n` is that of `y ↦ D(n², F y)`.

**Proof sketch.** The coin lengths agree, `B.coinLen n = D.coinLen (n²)` (`NUPPT.coinLen_eq`,
`PolyExpr.eval_subst`, `eval_mul`, `eval_var`); reindex `B`'s coins along `finCongr`
(`EnsembleLemmas.acceptProb_coins_equiv`) and compare pointwise (`NUPPT.distinguisherL_eq`,
`NUPPT.runAt_eq`, `List.ofFn_congr`, the run equation). -/
theorem distAdv_distinguisherL_reparam {σ τ : Type*} [Fintype σ] [Fintype τ] {B D : NUPPT}
    (hc : B.coins = D.coins.subst (.mul .var .var)) {n : ℕ} (X : σ → List Bool) (Y : τ → List Bool)
    (F : List Bool → List Bool) (hrun : ∀ y r, B.runAtL n y r = D.runAtL (n * n) (F y) r) :
    distAdv X Y (B.distinguisherL n) = distAdv X Y fun y c => D.distinguisherL (n * n) (F y) c := by
  have hlen : D.coinLen (n * n) = B.coinLen n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hc, PolyExpr.eval_subst, PolyExpr.eval_mul,
      PolyExpr.eval_var]
  have key : ∀ (y : List Bool) (c : D.Coins (n * n)),
      B.distinguisherL n y ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)) c) =
        D.distinguisherL (n * n) (F y) c := by
    intro y c
    have hofn : List.ofFn ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)) c) =
        List.ofFn c := (List.ofFn_congr hlen c).symm
    rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq, hofn,
      hrun]
  have hX := EnsembleLemmas.acceptProb_coins_equiv
    (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)) X (B.distinguisherL n)
  have hY := EnsembleLemmas.acceptProb_coins_equiv
    (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)) Y (B.distinguisherL n)
  simp only [key] at hX hY
  rw [distAdv_def, distAdv_def, ← hX, ← hY]

/-- **The hiding bound for the fixed reductions** [PS10, proof of Proposition 128.8, "by the
hiding property of the commitment"] (gate 03g review §2.1, items 3–6): for a commitment scheme
`(Com, ℓ)`, an efficient `V'`, a distinguisher `D` and an advice bound `b`, there is a negligible
`ε ≥ 0` such that for every `n`, every two colour vectors `v, v'` of `n` values of `n` bits and
every advice `adv` of length at most `b(n)`, the advantage of `cv ↦ D(n², hidingView V' adv cv)`
between the commitment vectors to `v` and to `v'` is at most `ε n`.

**Proof sketch.** At each `n` the triples `(v, v', adv)` with `|adv| ≤ b(n)` form a finite set
(the advice as `List.ofFn` of a tuple of length `≤ b(n)`); take one with the largest advantage
(`Finite.exists_max`) and hard-wire its advice as `α n`. The machine `B` of
`exists_colHidingRed` has, at parameter `n`, exactly that advantage on its own vectors
(`distAdv_distinguisherL_reparam`), which `Commitment.multiHiding` with `q := var` bounds by a
negligible `ε_B n` (`rw [PolyExpr.eval_var] at`, pre-ship probe R3b); `ε := |ε_B|` is
nonnegative and negligible and bounds every triple's advantage. -/
theorem exists_hidingView_bound {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {V' : Strategy} (hV' : V'.Efficient) (D : NUPPT) (b : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧ ∀ n (v v' : Fin n → Fin n → Bool)
      (adv : List Bool), adv.length ≤ b.eval n →
        distAdv (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com v r)
          (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
          (fun cv d => D.distinguisherL (n * n) (hidingView V' adv cv) d) ≤ ε n := by
  -- the advantage of a triple, the advice given as a tuple of length at most `b(n)`
  let g : ∀ n, (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) ×
      (Σ k : Fin (b.eval n + 1), Fin k → Bool) → ℝ := fun n p =>
    distAdv (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com p.1 r)
      (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com p.2.1 r)
      (fun cv d => D.distinguisherL (n * n) (hidingView V' (List.ofFn p.2.2.2) cv) d)
  have hmax : ∀ n, ∃ p, ∀ q, g n q ≤ g n p := fun n => Finite.exists_max (g n)
  choose p hp using hmax
  have hα : ∀ n, (List.ofFn (p n).2.2.2).length ≤ b.eval n := fun n => by
    rw [List.length_ofFn]
    exact Nat.lt_succ_iff.1 (p n).2.2.1.isLt
  obtain ⟨B, hBc, hB⟩ := exists_colHidingRed hV' D (fun n => List.ofFn (p n).2.2.2) b hα
  obtain ⟨ε, hε, hεB⟩ := hC.multiHiding .var B
  refine ⟨fun n => |ε n|, hε.mono ⟨0, fun n _ => (abs_abs _).le⟩, fun n => abs_nonneg _,
    fun n v v' adv hadv => ?_⟩
  have h := hεB n
  rw [PolyExpr.eval_var] at h
  have hB' := distAdv_distinguisherL_reparam hBc
    (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (p n).1 r)
    (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (p n).2.1 r) _ (hB n)
  have hq : g n (v, v', ⟨⟨adv.length, Nat.lt_succ_of_le hadv⟩, adv.get⟩) ≤ g n (p n) := hp n _
  have hofn : List.ofFn adv.get = adv := List.ofFn_get adv
  simp only [g, hofn] at hq
  calc _ ≤ _ := hq
    _ = _ := hB'.symm
    _ ≤ ε n := h (p n).1 (p n).2.1
    _ ≤ |ε n| := le_abs_self _

/-- The edgeless advice is short: at most `4 (2M + 2)` bits when `x`, `z`, `ρ` have at most `M`
(`CommitmentLemmas.length_encodeMsgs_le`). -/
theorem length_edgelessAdv_le {M : ℕ} {x z ρ : List Bool} (hx : x.length ≤ M)
    (hz : z.length ≤ M) (hρ : ρ.length ≤ M) : (edgelessAdv x z ρ).length ≤ 4 * (2 * M + 2) := by
  rw [edgelessAdv_eq]
  refine CommitmentLemmas.length_encodeMsgs_le _ M fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  exacts [hx, hz, hρ, Nat.zero_le _]

/-- The planted advice is short: at most `15 (2M + 2)` bits when each of its fields has at most
`M` bits.

**Proof sketch.** `CommitmentLemmas.length_encodeMsgs_le` on the fifteen fields of
`plantedAdv_eq`: the unary fields have their numbers as lengths (`List.length_replicate`), the
flags at most one bit, and the optional earlier outcome is empty or bounded by `hpre`. -/
theorem length_plantedAdv_le {M : ℕ} {x z ρ A₁ A₂ opn post : List Bool} {n p₁ p₂ m e₀ : ℕ}
    {pre : Option (List Bool)} (h1 : 1 ≤ M) (hx : x.length ≤ M) (hz : z.length ≤ M)
    (hρ : ρ.length ≤ M) (hn : n ≤ M) (hp₁ : p₁ ≤ M) (hp₂ : p₂ ≤ M) (hA₁ : A₁.length ≤ M)
    (hA₂ : A₂.length ≤ M) (hm : m ≤ M) (he₀ : e₀ ≤ M) (hopn : opn.length ≤ M)
    (hpost : post.length ≤ M) (hpre : ∀ v, pre = some v → v.length ≤ M) :
    (plantedAdv x z ρ n p₁ p₂ A₁ A₂ m e₀ opn post pre).length ≤ 15 * (2 * M + 2) := by
  rw [plantedAdv_eq]
  refine CommitmentLemmas.length_encodeMsgs_le _ M fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact hx
  · exact hz
  · exact hρ
  · exact h1
  · split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega
  · rw [List.length_replicate]; exact hn
  · rw [List.length_replicate]; exact hp₁
  · rw [List.length_replicate]; exact hp₂
  · exact hA₁
  · exact hA₂
  · rw [List.length_replicate]; exact hm
  · rw [List.length_replicate]; exact he₀
  · exact hopn
  · exact hpost
  · cases pre with
    | none => exact Nat.zero_le _
    | some v => exact hpre v rfl

/-- `D`'s advantage does not depend on how its parameter is written: `N₁ = N₂` gives equal
advantages of `cv ↦ D(N₁, F cv)` and `cv ↦ D(N₂, F cv)` (the transport of `D`'s coin type along
`|encGraph G| = n²`). -/
theorem distAdv_distinguisherL_congr {σ τ : Type*} [Fintype σ] [Fintype τ] (D : NUPPT)
    {N₁ N₂ : ℕ} (h : N₁ = N₂) (X : σ → List Bool) (Y : τ → List Bool) (F : List Bool → List Bool) :
    distAdv X Y (fun cv d => D.distinguisherL N₁ (F cv) d) =
      distAdv X Y fun cv d => D.distinguisherL N₂ (F cv) d := by
  subst h
  rfl

end TCSlib.Cryptography.ColZK
