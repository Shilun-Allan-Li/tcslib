/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: efficiency of the honest parties

The polynomial-time machines behind the honest parties of [PS10, Protocols 118.3 and 120.6]
(inventory item Inf-4.2) and the decider of the witness relation `R_iso`, proved for the
shadow strategies of `GraphIsomorphism/Proofs.lean` (the main file
`ZeroKnowledge/GraphIsomorphism.lean` closes its targets by `exact GI.…`).

Every strategy is exhibited as a polynomial-time function of the interactive machine layout
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`GI.efficient_of_polyTime`), assembled from the FP
calculus of `TCSlib.Complexity.ClassNP.PolyTimePairing`, the state-loop toolkit of
`TCSlib.Complexity.Randomized.Build.StateLoop`, the typed coin cuts of
`TCSlib.Complexity.Randomized.Primitives`, and the three string operations of
`ZeroKnowledge/Encoding.lean` (`polyTimeComputable_encPermGraph`,
`polyTimeComputable_encPermMulInv`, `polyTimeComputable_encPermFromCoins`), used as black
boxes. The two new devices are the **unary square root** `w ↦ 1^{√|w|}` (a state loop
counting up to the first `i` with `|w| < (i+1)²`), which reads the vertex count off the common
input, and the **padding** `padSq n w` of a graph word to length `n²`, which lets the
`encPermGraph` machine (whose vertex count is `√` of the length of the graph word) relabel a
graph decoded on a *given* vertex count (`decGraphAt n w`, as the verifiers do on possibly
malformed inputs).

## Main definitions

* `TCSlib.Cryptography.GI.padSq` — a graph word padded to length `n²`.
* `TCSlib.Cryptography.GI.relabelAt`, `GI.sampleStr`, `GI.mulInvStr` — the three string
  operations of the honest parties as functions of words (vertex count passed in unary).
* `TCSlib.Cryptography.GI.argX`, `GI.argZ`, `GI.argM`, `GI.vcount` — the projections of the
  interactive layout.
* `TCSlib.Cryptography.GI.risoTest` — the decider of `R_iso`.

## Main results

* `TCSlib.Cryptography.GI.stateFind` — the state-loop form of the repetition lemma (copy of the
  private `polyTimeComputable_stateFind` of `Randomized/Repetition.lean`).
* `TCSlib.Cryptography.GI.unarySqrt_poly` — `w ↦ 1^{√|w|}` is polynomial-time.
* `TCSlib.Cryptography.GI.wellFormed_poly` — the well-formedness test is polynomial-time.
* `TCSlib.Cryptography.GI.encPermGraphAt_poly` — relabelling a graph decoded on a given vertex
  count is polynomial-time.
* `TCSlib.Cryptography.GI.Riso_decidable` — the decider clause of `Riso_witnessRelation`.
* `TCSlib.Cryptography.GI.giProver_efficient`, `GI.giVerifier_efficient`,
  `GI.gniVerifier_efficient` — the single-iteration parties are PPT strategies.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Complexity.StateLoop

/-! ### An FP toolkit -/

/-- Polynomial-time computability transfers along pointwise equality. -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- The pair-validity test `x ↦ [(pairDecode x).isSome]` is polynomial-time
(`Turing.FinTM.computesFunInTime_pairValid`). -/
theorem pairValid_poly : PolyTimeComputable fun x => [(pairDecode x).isSome] := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_pairValid
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- State loops (copy of `polyTimeComputable_stateFind` of
`TCSlib.Complexity.Randomized.Repetition`, which is private there): a state word `⟨x, s⟩`
evolving from `start x` by `step`, a test `acc` first true at round `N x ≤ R|x|`, states of
length `≤ B|x|` up to that round; then `x ↦ out ⟨x, orbit x (N x)⟩` is polynomial-time.

**Proof sketch.** `Complexity.polyTimeComputable_iterateFind` on the guarded step
`StateLoop.gstep step B` (orbit bound `StateLoop.length_gstep_iterate_le` for every word),
pre-composed with `x ↦ ⟨x, start x⟩`; on the genuine orbit the guard never fires
(`StateLoop.gstep_iterate_eq`) and `List.find?` returns `N x` (`StateLoop.find?_range_eq_some`). -/
theorem stateFind {start step : List Bool → List Bool}
    {acc : List Bool → Bool} {out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hacc : PolyTimeComputable fun w => [acc w]) (hout : PolyTimeComputable out)
    (R B : PolyExpr) (N : List Bool → ℕ) (hN : ∀ x, N x ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ N x → (orbit start step x i).length ≤ B.eval x.length)
    (hfirst : ∀ x i, i < N x → acc (pairEncode x (orbit start step x i)) = false)
    (hlast : ∀ x, acc (pairEncode x (orbit start step x (N x))) = true) :
    PolyTimeComputable fun x => out (pairEncode x (orbit start step x (N x))) := by
  have hF := polyTimeComputable_iterateFind (gstep_poly hstep B) hacc hout R (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  convert hF.comp hpre using 1
  funext x
  simp only [Function.comp_apply]
  have horb := gstep_iterate_eq start step B x (N x) (hbound x)
  have hle : N x ≤ R.eval (pairEncode x (start x)).length :=
    (hN x).trans (R.eval_mono (by rw [length_pairEncode]; omega))
  have hfind : (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((gstep step B)^[i] (pairEncode x (start x)))) = some (N x) := by
    apply find?_range_eq_some hle
    · intro i hi
      rw [horb i hi.le]
      exact hfirst x i hi
    · rw [horb (N x) le_rfl]
      exact hlast x
  rw [hfind]
  exact (congrArg out (horb (N x) le_rfl)).symm

/-! ### The unary square root -/

namespace SqrtLoop

/-- The initial state: the empty counter. -/
def start (_w : List Bool) : List Bool := []

/-- The step on the state word `⟨w, 1^i⟩`: the counter `1^{i+1}`. -/
def step (st : List Bool) : List Bool := true :: pairSndD st

/-- The test on `⟨w, 1^i⟩`: `|w| < (i + 1)²`, first true at `i = √|w|`. -/
def acc (st : List Bool) : Bool := decide ((pairFstD st).length < ((pairSndD st).length + 1) ^ 2)

/-- The output on `⟨w, 1^i⟩`: the counter. -/
def out (st : List Bool) : List Bool := pairSndD st

/-- The closed form of the orbit: the counter `1^i` after `i` rounds. -/
theorem orbit_eq (w : List Bool) (i : ℕ) : orbit start step w i = List.replicate i true := by
  induction i with
  | zero => rfl
  | succ i ih => simp [step, ih, List.replicate_succ]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start := polyTimeComputable_const []

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step := (cons_poly true).comp polyTimeComputable_pairSndD

/-- The test is polynomial-time: the negated length comparison of `w` with `1^{(i+1)²}`. -/
theorem acc_poly : PolyTimeComputable fun st => [acc st] := by
  have h := not_poly (lenLe_comp polyTimeComputable_pairFstD
    (unaryPoly_comp (.normal 1 2) polyTimeComputable_pairSndD))
  refine ptc_congr h fun st => ?_
  simp only [acc, List.length_replicate, PolyExpr.eval_normal, one_mul]
  exact congrArg (fun b => [b]) (by rw [← decide_not]; exact decide_eq_decide.2 not_le.symm)

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := polyTimeComputable_pairSndD

end SqrtLoop

/-- **The unary square root is polynomial-time:** `w ↦ 1^{√|w|}` (the vertex count of an
encoded graph read off its length). A state loop counting up to the first `i` with
`|w| < (i + 1)²` (`Nat.le_sqrt'`, `Nat.lt_succ_sqrt'`), at most `|w|` rounds. -/
theorem unarySqrt_poly : PolyTimeComputable fun w => List.replicate (Nat.sqrt w.length) true := by
  have h := stateFind SqrtLoop.start_poly SqrtLoop.step_poly SqrtLoop.acc_poly SqrtLoop.out_poly
    .var .var (fun w => Nat.sqrt w.length) (fun w => Nat.sqrt_le_self _)
    (fun w i hi => by
      rw [SqrtLoop.orbit_eq, List.length_replicate]
      exact hi.trans (Nat.sqrt_le_self _))
    (fun w i hi => by
      simp only [SqrtLoop.acc, SqrtLoop.orbit_eq, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, decide_eq_false_iff_not, not_lt]
      exact Nat.le_sqrt'.1 hi)
    (fun w => by
      simp only [SqrtLoop.acc, SqrtLoop.orbit_eq, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, decide_eq_true_eq]
      exact Nat.lt_succ_sqrt' _)
  refine ptc_congr h fun w => ?_
  simp [SqrtLoop.out, SqrtLoop.orbit_eq]

/-! ### Well-formedness of an instance -/

/-- The well-formedness test of a common input is polynomial-time: the pair-validity test and
two length comparisons against `1^{n²}` for `n = √|fst x|` in unary (`unarySqrt_poly`,
`polyTimeComputable_unaryPoly`, `polyTimeComputable_lenEq`). -/
theorem wellFormed_poly : PolyTimeComputable fun x => [wellFormedInstance x] := by
  have hsq : PolyTimeComputable fun x => List.replicate
      ((PolyExpr.mul .var .var).eval (List.replicate (Nat.sqrt (pairFstD x).length) true).length) true :=
    unaryPoly_comp (.mul .var .var) (unarySqrt_poly.comp polyTimeComputable_pairFstD)
  have h1 := polyTimeComputable_lenEq.comp (polyTimeComputable_pairFstD.pairEncode hsq)
  have h2 := polyTimeComputable_lenEq.comp (polyTimeComputable_pairSndD.pairEncode hsq)
  have h := polyTimeComputable_and pairValid_poly (polyTimeComputable_and h1 h2)
  refine ptc_congr h fun x => ?_
  simp only [wellFormedInstance, instanceVertexCount, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_var, Bool.decide_and, Bool.decide_eq_true]

/-! ### Padding a graph word to a given vertex count -/

/-- The graph word `w` padded with `false` (or cut) to length `n²`: it decodes on `n` vertices
to the same graph as `w` (`decGraphAt_padSq`) and its length determines `n`. -/
def padSq (n : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate (n * n) false).take (n * n)

/-- The padded word has length `n²`. -/
theorem length_padSq (n : ℕ) (w : List Bool) : (padSq n w).length = n * n := by
  simp [padSq, List.length_take, List.length_append]

/-- The vertex count read off the padded word is `n`. -/
theorem sqrt_length_padSq (n : ℕ) (w : List Bool) : Nat.sqrt (padSq n w).length = n := by
  rw [length_padSq, Nat.sqrt_eq]

/-- Below `n²` the padded word reads as `w` with default `false`. -/
theorem getD_padSq (n : ℕ) (w : List Bool) {k : ℕ} (hk : k < n * n) :
    (padSq n w).getD k false = w.getD k false := by
  simp only [padSq, List.getD_eq_getElem?_getD, List.getElem?_take, hk, if_true, List.getElem?_append]
  split_ifs with h
  · rfl
  · rw [List.getElem?_replicate, if_pos (by omega), Option.getD_some,
      List.getElem?_eq_none (by omega)]
    rfl

/-- Padding does not change the decoded graph on `n` vertices. -/
theorem decGraphAt_padSq (n : ℕ) (w : List Bool) : decGraphAt n (padSq n w) = decGraphAt n w :=
  funext fun u => funext fun v => getD_padSq n w (finProdFinEquiv (u, v)).isLt

/-- `w ↦ 0^{|w|}` is polynomial-time (`polyTimeComputable_pairXor` on `⟨w, w⟩`). -/
theorem zeros_poly : PolyTimeComputable fun w => List.replicate w.length false :=
  ptc_congr (polyTimeComputable_pairXor.comp (polyTimeComputable_id.pairEncode polyTimeComputable_id))
    fun w => by simp

/-- Padding to the square of a unary count is polynomial-time: on `⟨u, w⟩`, `padSq |u| w`
(`polyTimeComputable_pairTakePoly` at `n²` on `⟨u, w ++ 0^{|u|²}⟩`). -/
theorem padSq_poly : PolyTimeComputable fun z => padSq (pairFstD z).length (pairSndD z) := by
  have hsq : PolyTimeComputable fun z =>
      List.replicate ((PolyExpr.mul .var .var).eval (pairFstD z).length) true :=
    unaryPoly_comp (.mul .var .var) polyTimeComputable_pairFstD
  have hz := zeros_poly.comp hsq
  have hcat := polyTimeComputable_pairSndD.append hz
  have h := (polyTimeComputable_pairTakePoly (.mul .var .var)).comp
    (polyTimeComputable_pairFstD.pairEncode hcat)
  refine ptc_congr h fun z => ?_
  simp [padSq, PolyExpr.eval_mul]

/-! ### The three string operations of the honest parties, as functions of words -/

/-- `encGraph (π(G))` for the graph `G` decoded from `w` on `|u|` vertices and the permutation
`π` decoded from `p` on `|u|` points (the vertex count is passed in unary so that it is an
ordinary argument, not read off `w`). -/
noncomputable def relabelAt (u w p : List Bool) : List Bool :=
  encGraph (permGraph (decGraphAt u.length w) (decPerm u.length p))

/-- `relabelAt` with the vertex count `1^n`. -/
theorem relabelAt_replicate (n : ℕ) (w p : List Bool) :
    relabelAt (List.replicate n true) w p = encGraph (permGraph (decGraphAt n w) (decPerm n p)) := by
  unfold relabelAt
  rw [List.length_replicate]

/-- The permutation sampled from the tape `r` on the vertex count of the graph word `w`, as a
string (`samplePerm` at `√|w|`). -/
noncomputable def sampleStr (w r : List Bool) : List Bool := encPerm (samplePerm (Nat.sqrt w.length) r)

/-- The product `π σ⁻¹` of the permutations decoded from `p` and `y` on `√|p|` points, as a
string (the function of `polyTimeComputable_encPermMulInv`). -/
noncomputable def mulInvStr (p y : List Bool) : List Bool :=
  encPerm (decPerm (Nat.sqrt p.length) p * (decPerm (Nat.sqrt p.length) y)⁻¹)

/-- The product machine on `⟨encPerm π, y⟩` returns `encPerm (π σ⁻¹)` for `σ = decPerm n y`
(`length_encPerm`, `Nat.sqrt_eq`, `decPerm_encPerm`). -/
theorem mulInvStr_encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) (y : List Bool) :
    mulInvStr (encPerm π) y = encPerm (π * (decPerm n y)⁻¹) := by
  have h : Nat.sqrt (encPerm π).length = n := by rw [length_encPerm, Nat.sqrt_eq]
  unfold mulInvStr
  rw [h, decPerm_encPerm]

/-- Sampling the vertex permutation of a graph word from a tape is polynomial-time
(the shared `polyTimeComputable_encPermFromCoins` of `ZeroKnowledge/Encoding.lean`, whose
vertex count `(decGraph w).1` is `√|w|`). -/
theorem sampleStr_poly : PolyTimeComputable fun z => sampleStr (pairFstD z) (pairSndD z) :=
  polyTimeComputable_encPermFromCoins

/-- The permutation product is polynomial-time (`polyTimeComputable_encPermMulInv`). -/
theorem mulInvStr_poly : PolyTimeComputable fun z => mulInvStr (pairFstD z) (pairSndD z) :=
  polyTimeComputable_encPermMulInv

/-- **Relabelling a graph decoded on a given vertex count is polynomial-time:** on
`⟨u, ⟨w, p⟩⟩`, `relabelAt u w p` (`polyTimeComputable_encPermGraph` on the padded word
`padSq |u| w`, whose decoding is `⟨|u|, decGraphAt |u| w⟩`). -/
theorem relabelAt_poly :
    PolyTimeComputable fun z => relabelAt (pairFstD z) (pairFstD (pairSndD z)) (pairSndD (pairSndD z)) := by
  have hpad : PolyTimeComputable fun z => padSq (pairFstD z).length (pairFstD (pairSndD z)) :=
    ptc_congr (padSq_poly.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))) fun z => by simp
  have h := polyTimeComputable_encPermGraph.comp
    (hpad.pairEncode (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  refine ptc_congr h fun z => ?_
  simp only [Function.comp_apply]
  rw [pairFstD_pairEncode, pairSndD_pairEncode, decGraph_eq_of_sqrt (sqrt_length_padSq _ _)]
  simp only [relabelAt, decGraphAt_padSq]

/-! ### The interactive layout and its projections -/

/-- The common-input slot of the interactive layout. -/
def argX (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inArg w))

/-- The auxiliary-input slot of the interactive layout. -/
def argZ (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg w))

/-- The encoded-messages slot of the interactive layout. -/
def argM (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

/-- The vertex count of the common input of the layout. -/
def vcount (w : List Bool) : ℕ := Nat.sqrt (pairFstD (argX w)).length

/-- The common input of a layout. -/
@[simp] theorem argX_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argX (ilayout x z hist r) = x := by
  simp [argX, ilayout]

/-- The auxiliary input of a layout. -/
@[simp] theorem argZ_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argZ (ilayout x z hist r) = z := by
  simp [argZ, ilayout]

/-- The encoded messages of a layout. -/
@[simp] theorem argM_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argM (ilayout x z hist r) = Strategy.encodeMsgs hist := by
  simp [argM, ilayout]

/-- The coins of a layout. -/
@[simp] theorem inCoins_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    NUPPT.inCoins (ilayout x z hist r) = r := by
  simp [ilayout]

/-- The unary parameter of a layout. -/
@[simp] theorem inParam_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    NUPPT.inParam (ilayout x z hist r) = List.replicate x.length true := by
  simp [ilayout]

/-- The vertex count of a layout. -/
@[simp] theorem vcount_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    vcount (ilayout x z hist r) = Nat.sqrt (pairFstD x).length := by
  simp [vcount]

/-- The common-input projection is polynomial-time. -/
theorem argX_poly : PolyTimeComputable argX :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The auxiliary-input projection is polynomial-time. -/
theorem argZ_poly : PolyTimeComputable argZ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The messages projection is polynomial-time. -/
theorem argM_poly : PolyTimeComputable argM :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-- The first graph word of the common input. -/
theorem w₀_poly : PolyTimeComputable fun w => pairFstD (argX w) := polyTimeComputable_pairFstD.comp argX_poly

/-- The second graph word of the common input. -/
theorem w₁_poly : PolyTimeComputable fun w => pairSndD (argX w) := polyTimeComputable_pairSndD.comp argX_poly

/-- The vertex count in unary. -/
theorem vcount_poly : PolyTimeComputable fun w => List.replicate (vcount w) true :=
  unarySqrt_poly.comp w₀_poly

/-- The first bit of the coins (the challenge of the verifiers). -/
theorem coinBit_poly : PolyTimeComputable fun w => [(NUPPT.inCoins w).headD false] :=
  headBit_poly.comp NUPPT.polyTimeComputable_inCoins

/-- The graph word selected by the first coin, `G_b`. -/
theorem selGraph_poly : PolyTimeComputable fun w =>
    if (NUPPT.inCoins w).headD false then pairSndD (argX w) else pairFstD (argX w) :=
  polyTimeComputable_ite coinBit_poly w₁_poly w₀_poly

/-- Relabelling the graph word `g w` on `vcount w` vertices by the permutation word `p w`. -/
theorem relabel_poly {g p : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hp : PolyTimeComputable p) :
    PolyTimeComputable fun w => relabelAt (List.replicate (vcount w) true) (g w) (p w) :=
  ptc_congr (relabelAt_poly.comp (vcount_poly.pairEncode (hg.pairEncode hp))) fun w => by simp

/-- The sampled permutation of a party as a string, from the common input and the coins. -/
theorem piStr_poly : PolyTimeComputable fun w => sampleStr (pairFstD (argX w)) (NUPPT.inCoins w) :=
  ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode NUPPT.polyTimeComputable_inCoins)) fun w => by simp

/-! ### The witness relation `R_iso` -/

/-- The test "`y` is a genuine permutation encoding": `encPerm (decPerm n y) = y`, computed by the
product machine against the identity `decPerm n [] = 1`. -/
noncomputable def permTest (y : List Bool) : Bool := decide (mulInvStr y [] = y)

/-- The test `encGraph (σ(G₀)) = w₁` for `G₀` decoded from `w₀` and `σ` from `y`. -/
noncomputable def graphTest (w₀ w₁ y : List Bool) : Bool :=
  decide (relabelAt (List.replicate (Nat.sqrt w₀.length) true) w₀ y = w₁)

/-- A permutation encoding passes `permTest`. -/
theorem permTest_encPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : permTest (encPerm σ) = true := by
  simp [permTest, mulInvStr_encPerm, decPerm_nil]

/-- A word of length `n²` passing `permTest` is the encoding of its decoded permutation. -/
theorem eq_encPerm_of_permTest {n : ℕ} {y : List Bool} (hlen : y.length = n * n)
    (h : permTest y = true) : y = encPerm (decPerm n y) := by
  have hn : Nat.sqrt y.length = n := by rw [hlen, Nat.sqrt_eq]
  simp only [permTest, mulInvStr, decide_eq_true_eq] at h
  rw [hn, decPerm_nil, inv_one, mul_one] at h
  exact h.symm

/-- `graphTest` on an encoded graph. -/
theorem graphTest_encGraph {n : ℕ} (G₀ : Graph n) (w₁ y : List Bool) :
    graphTest (encGraph G₀) w₁ y = decide (encGraph (permGraph G₀ (decPerm n y)) = w₁) := by
  unfold graphTest
  rw [length_encGraph, Nat.sqrt_eq, relabelAt_replicate, decGraphAt_encGraph]

/-- The decider of `R_iso` on `⟨x, y⟩`: `x` well formed, `|y| = |fst x|`, `y` a genuine
permutation encoding, and `encGraph (σ(G₀)) = snd x`. -/
noncomputable def risoTest (z : List Bool) : Bool :=
  wellFormedInstance (pairFstD z) &&
    (decide ((pairSndD z).length = (pairFstD (pairFstD z)).length) &&
      (permTest (pairSndD z) && graphTest (pairFstD (pairFstD z)) (pairSndD (pairFstD z)) (pairSndD z)))

/-- The decider of `R_iso` is polynomial-time (`wellFormed_poly`, `polyTimeComputable_lenEq`,
`mulInvStr_poly`, `relabelAt_poly`, `polyTimeComputable_pairEq`). -/
theorem risoTest_poly : PolyTimeComputable fun z => [risoTest z] := by
  have hw0 : PolyTimeComputable fun z => pairFstD (pairFstD z) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hw1 : PolyTimeComputable fun z => pairSndD (pairFstD z) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have h1 : PolyTimeComputable fun z => [wellFormedInstance (pairFstD z)] :=
    wellFormed_poly.comp polyTimeComputable_pairFstD
  have h2 : PolyTimeComputable fun z => [decide ((pairSndD z).length = (pairFstD (pairFstD z)).length)] :=
    ptc_congr (polyTimeComputable_lenEq.comp (polyTimeComputable_pairSndD.pairEncode hw0))
      fun z => by simp
  have h3 : PolyTimeComputable fun z => [permTest (pairSndD z)] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((mulInvStr_poly.comp
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))).pairEncode
        polyTimeComputable_pairSndD)) fun z => by simp [permTest]
  have h4 : PolyTimeComputable fun z => [graphTest (pairFstD (pairFstD z)) (pairSndD (pairFstD z)) (pairSndD z)] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((relabelAt_poly.comp
      ((unarySqrt_poly.comp hw0).pairEncode (hw0.pairEncode polyTimeComputable_pairSndD))).pairEncode hw1))
      fun z => by simp [graphTest]
  exact polyTimeComputable_and h1 (polyTimeComputable_and h2 (polyTimeComputable_and h3 h4))

/-- The decider of `R_iso` is correct: `risoTest ⟨x, y⟩ = true ↔ Riso x y`.

**Proof sketch.** (→) A well-formed `x` is `encInstance G₀ G₁` (`eq_encInstance_of_wellFormed`);
`|y| = n²` and `permTest` give `y = encPerm σ` for `σ := decPerm n y` (`eq_encPerm_of_permTest`),
and the graph test reads `encGraph (σ(G₀)) = encGraph G₁`, i.e. `σ(G₀) = G₁`
(`graphTest_encGraph`, `encGraph_injective`). (←) Unfold the witnesses and evaluate
(`wellFormedInstance_encInstance`, `length_encPerm`, `permTest_encPerm`, `decPerm_encPerm`). -/
theorem risoTest_iff (x y : List Bool) : risoTest (pairEncode x y) = true ↔ Riso x y := by
  simp only [risoTest, pairFstD_pairEncode, pairSndD_pairEncode, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hwf, hlen, hperm, hgraph⟩
    obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
    have h0 : pairFstD (encInstance G₀ G₁) = encGraph G₀ := pairFstD_pairEncode _ _
    have h1 : pairSndD (encInstance G₀ G₁) = encGraph G₁ := pairSndD_pairEncode _ _
    rw [h0, length_encGraph] at hlen
    rw [h0, h1, graphTest_encGraph, decide_eq_true_eq] at hgraph
    exact ⟨n, G₀, G₁, decPerm n y, rfl, eq_encPerm_of_permTest hlen hperm, encGraph_injective n hgraph⟩
  · rintro ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩
    refine ⟨wellFormedInstance_encInstance G₀ G₁, by simp, permTest_encPerm σ, ?_⟩
    rw [pairFstD_pairEncode, pairSndD_pairEncode, graphTest_encGraph, decPerm_encPerm, hσ]
    exact decide_eq_true rfl

/-- The decider clause of `Riso_witnessRelation` (Def-191.11 for `R_iso`). -/
theorem Riso_decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ Riso x y :=
  ⟨risoTest, risoTest_poly, risoTest_iff⟩

/-! ### Efficiency of the single-iteration parties -/

/-- The honest prover of the graph isomorphism protocol is a PPT strategy
[PS10, Proposition 120.7] (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime` with the layout function: message `1` is
`relabel_poly` of `G₀` by the sampled permutation (`piStr_poly`), message `3` is
`mulInvStr_poly` on `⟨encPerm π, y⟩` or `encPerm π` according to the challenge bit
(`polyTimeComputable_ite`), the case split on `msgs = []` by `isNil_poly`. The equation with
`giProver.next` is checked on the two shapes of the history (`giProver_next_nil'`,
`giProver_next_cons'`) with `relabelAt_replicate`, `decPerm_encPerm`, `mulInvStr_encPerm`. -/
theorem giProver_efficient : giProver.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (argM w = [])] := isNil_poly.comp argM_poly
  have hbit : PolyTimeComputable fun w => [(pairFstD (argM w)).headD false] :=
    headBit_poly.comp (polyTimeComputable_pairFstD.comp argM_poly)
  have hF₁ := relabel_poly w₀_poly piStr_poly
  have hmul : PolyTimeComputable fun w =>
      mulInvStr (sampleStr (pairFstD (argX w)) (NUPPT.inCoins w)) (argZ w) :=
    ptc_congr (mulInvStr_poly.comp (piStr_poly.pairEncode argZ_poly)) fun w => by simp
  have hF₃ : PolyTimeComputable fun w => if (pairFstD (argM w)).headD false then
      mulInvStr (sampleStr (pairFstD (argX w)) (NUPPT.inCoins w)) (argZ w)
    else sampleStr (pairFstD (argX w)) (NUPPT.inCoins w) := polyTimeComputable_ite hbit hmul piStr_poly
  refine efficient_of_polyTime giProver (polyTimeComputable_ite hnil hF₁ hF₃) ?_
  intro x z r hist
  cases hist with
  | nil =>
    rw [giProver_next_nil']
    simp only [argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true, vcount_ilayout,
      argX_ilayout, inCoins_ilayout]
    rw [relabelAt_replicate, sampleStr, decPerm_encPerm]
    rfl
  | cons m h =>
    rw [giProver_next_cons']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, pairEncode_ne_nil, decide_false,
      Bool.false_eq_true, if_false, pairFstD_pairEncode, argX_ilayout, inCoins_ilayout, argZ_ilayout]
    rw [sampleStr, mulInvStr_encPerm]
    split_ifs <;> rfl

/-- The verifier of the graph isomorphism protocol is a PPT strategy [PS10, Definition 116.1
for Proposition 120.7] (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the challenge is the first coin (`coinBit_poly`),
the verdict conjoins the well-formedness test (`wellFormed_poly`) with `relabel_poly` of `G_b`
by `γ` compared with `H` (`polyTimeComputable_pairEq`); the number of messages is read off the
nesting of `msgs` by `isNil_poly` tests. The equation with `giVerifier.next` is checked on the
four shapes of the history (`giVerifier_next_nil'`, `giVerifier_next_one`,
`giVerifier_next_two'`, `giVerifier_next_long'`). -/
theorem giVerifier_efficient : giVerifier.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (argM w = [])] := isNil_poly.comp argM_poly
  have hnil₂ : PolyTimeComputable fun w => [decide (pairSndD (argM w) = [])] :=
    isNil_poly.comp (polyTimeComputable_pairSndD.comp argM_poly)
  have hnil₃ : PolyTimeComputable fun w => [decide (pairSndD (pairSndD (argM w)) = [])] :=
    isNil_poly.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp argM_poly))
  have hH : PolyTimeComputable fun w => pairFstD (argM w) := polyTimeComputable_pairFstD.comp argM_poly
  have hγ : PolyTimeComputable fun w => pairFstD (pairSndD (argM w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp argM_poly)
  have hcheck : PolyTimeComputable fun w => [decide (relabelAt (List.replicate (vcount w) true)
      (if (NUPPT.inCoins w).headD false then pairSndD (argX w) else pairFstD (argX w))
      (pairFstD (pairSndD (argM w))) = pairFstD (argM w))] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((relabel_poly selGraph_poly hγ).pairEncode hH))
      fun w => by simp
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf hcheck
  have hF := polyTimeComputable_ite hnil (polyTimeComputable_const [false])
    (polyTimeComputable_ite hnil₂ coinBit_poly
      (polyTimeComputable_ite hnil₃ hverdict (polyTimeComputable_const [false])))
  refine efficient_of_polyTime giVerifier hF ?_
  intro x z r hist
  rcases hist with _ | ⟨H, _ | ⟨γ, _ | ⟨m, t⟩⟩⟩
  · rw [giVerifier_next_nil']
    simp only [argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true]
  · rw [giVerifier_next_one]
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairSndD_pairEncode, decide_true, if_true,
      inCoins_ilayout]
  · rw [giVerifier_next_two']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairSndD_pairEncode, pairFstD_pairEncode,
      decide_true, if_true, vcount_ilayout, argX_ilayout, inCoins_ilayout,
      Bool.decide_and, Bool.decide_eq_true]
    rw [relabelAt_replicate]
    split_ifs <;> rfl
  · rw [giVerifier_next_long']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, pairEncode_ne_nil, decide_false,
      Bool.false_eq_true, if_false, pairSndD_pairEncode]

/-- The verifier of one iteration of the graph non-isomorphism protocol is a PPT strategy
[PS10, Proposition 118.4] (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the first message is `relabel_poly` of `G_b` by
the permutation sampled from the coins after the first (`sampleStr_poly` on
`⟨fst x, tail r⟩`), the verdict compares the reply's bit with the first coin
(`polyTimeComputable_pairEq` on one-bit words) under the well-formedness test
(`wellFormed_poly`). The equation with `gniVerifier.next` is checked on the three shapes of
the history (`gniVerifier_next_nil'`, `gniVerifier_next_one`, `gniVerifier_next_long'`). -/
theorem gniVerifier_efficient : gniVerifier.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (argM w = [])] := isNil_poly.comp argM_poly
  have hnil₂ : PolyTimeComputable fun w => [decide (pairSndD (argM w) = [])] :=
    isNil_poly.comp (polyTimeComputable_pairSndD.comp argM_poly)
  have hσ : PolyTimeComputable fun w => sampleStr (pairFstD (argX w)) (NUPPT.inCoins w).tail :=
    ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode (tail_poly.comp NUPPT.polyTimeComputable_inCoins)))
      fun w => by simp
  have hF₀ := relabel_poly selGraph_poly hσ
  have hbit : PolyTimeComputable fun w =>
      [decide ([(pairFstD (argM w)).headD false] = [(NUPPT.inCoins w).headD false])] :=
    ptc_congr (polyTimeComputable_pairEq.comp
      ((headBit_poly.comp (polyTimeComputable_pairFstD.comp argM_poly)).pairEncode coinBit_poly))
      fun w => by simp
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf hbit
  have hF := polyTimeComputable_ite hnil hF₀
    (polyTimeComputable_ite hnil₂ hverdict (polyTimeComputable_const [false]))
  refine efficient_of_polyTime gniVerifier hF ?_
  intro x z r hist
  rcases hist with _ | ⟨b', _ | ⟨m, t⟩⟩
  · rw [gniVerifier_next_nil']
    simp only [argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true,
      vcount_ilayout, argX_ilayout, inCoins_ilayout, List.drop_one]
    rw [relabelAt_replicate, sampleStr, decPerm_encPerm]
    split_ifs <;> rfl
  · rw [gniVerifier_next_one]
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairSndD_pairEncode, pairFstD_pairEncode,
      decide_true, if_true, argX_ilayout, inCoins_ilayout, Bool.decide_and,
      Bool.decide_eq_true, List.cons.injEq, and_true]
  · rw [gniVerifier_next_long']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, pairEncode_ne_nil, decide_false,
      Bool.false_eq_true, if_false, pairSndD_pairEncode]

end TCSlib.Cryptography.GI
