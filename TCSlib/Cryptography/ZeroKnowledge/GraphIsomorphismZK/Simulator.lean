/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph isomorphism simulator as a polynomial-time machine

The machine behind Claim-123.d of `ZeroKnowledge/GraphIsomorphismZK.lean`
(`exists_giSimulator`): the string-level simulator of [PS10, Algorithm 123.4], truncated at
`n` attempts (D8), is a polynomial-time function of its machine layout
`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩`, hence a uniform `Complexity.NUPPT`.

The frozen string definitions of the main file (`giSimBlockLen`, `giSimCoins`,
`giSimAttemptStr`, `giSim`) are *shadowed* here by `GIZK.blockLen`, `GIZK.simCoins`,
`GIZK.attemptStr`, `GIZK.sim` with identical bodies, so that the machine can be built before
the main file; the main file identifies each shadow with its original by `rfl`.

One attempt at index `t` reads the `t`-th coin block (`coinSlice`, cut by the typed coin
cuts `Complexity.polyTimeComputable_pairTakePoly`/`pairDropPoly` with the block length in
unary), samples the permutation (`polyTimeComputable_encPermFromCoins`), relabels the guessed
graph (`polyTimeComputable_encPermGraph` on the padded graph word), runs the cheating
verifier's machine (`Strategy.Efficient`) and compares its challenge bit with the guess
(`polyTimeComputable_pairEq`). The loop over `t < n` is the bounded first-index search
`EncodingMachines.polyTimeComputable_firstIdx` (an instance of the repetition lemma
`Complexity.polyTimeComputable_iterateFind`), and `List.findSome?` over `List.range n` is
identified with the first accepted index (`findSome?_range_getD`).

## Main definitions

* `TCSlib.Cryptography.GIZK.blockLen`, `GIZK.simCoins`, `GIZK.attemptStr`, `GIZK.sim` —
  shadows of the string simulator of the main file.
* `TCSlib.Cryptography.GIZK.attemptAt` — the attempt at a given index on the simulator's
  machine layout.

## Main results

* `TCSlib.Cryptography.GIZK.attemptAt_poly` — the success test and the view of one attempt
  are polynomial-time functions of the indexed layout.
* `TCSlib.Cryptography.GIZK.sim_poly` — the simulator is a polynomial-time function of its
  layout.
* `TCSlib.Cryptography.GIZK.exists_simulator` — the simulator is a uniform PPT (Claim-123.d,
  shadow form).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge proofs, Algorithm 123.4, p. 123.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GIZK

open Complexity Turing Complexity.StateLoop EncodingMachines

/-! ### Shadows of the string simulator -/

/-- Shadow of `giSimBlockLen`: the coin block of one attempt against `V'` at instance length
`N` has one guessed bit, `(N + 1)²` permutation-sampling bits and `V'`'s tape. -/
def blockLen (V' : Strategy) (N : ℕ) : ℕ := 1 + (N + 1) ^ 2 + V'.coinLen N

/-- The block length as a syntactic polynomial of the instance length. -/
def blockPoly (V' : Strategy) : PolyExpr := .add (.add (.const 1) (.normal 1 2)) V'.coins

/-- `blockPoly` evaluates to `blockLen`. -/
theorem blockPoly_eval (V' : Strategy) (N : ℕ) : (blockPoly V').eval N = blockLen V' N := by
  simp [blockPoly, blockLen, PolyExpr.eval, PolyExpr.normal, Strategy.coinLen]

/-- Shadow of `giSimCoins`: `|x|` blocks of `blockLen V' |x|` bits. -/
def simCoins (V' : Strategy) : PolyExpr :=
  .mul .var (.add (.add (.const 1) (.normal 1 2)) V'.coins)

/-- The coin polynomial evaluates to `N` blocks of `blockLen V' N` bits. -/
theorem simCoins_eval (V' : Strategy) (N : ℕ) : (simCoins V').eval N = N * blockLen V' N := by
  simp [simCoins, blockLen, PolyExpr.eval, PolyExpr.normal, Strategy.coinLen]

/-- Shadow of `giSimAttemptStr`: one attempt of [PS10, Algorithm 123.4] on the coin block
`c = b' :: (permutation coins ++ V'`'s tape)`. -/
noncomputable def attemptStr (V' : Strategy) (x z c : List Bool) : Option (List Bool) :=
  let n := instanceVertexCount x
  let b' := c.headD false
  let π := samplePerm n ((c.drop 1).take ((x.length + 1) ^ 2))
  let rV := c.drop (1 + (x.length + 1) ^ 2)
  let H := encGraph (permGraph (if b' then instanceG₁ x else instanceG₀ x) π)
  if (V'.next x z rV [H]).headD false = b' then some (View.encode ⟨x, z, rV, [H, encPerm π]⟩)
  else none

/-- Shadow of `giSim`: up to `n = instanceVertexCount x` attempts on consecutive coin blocks,
the first successful view, or `[]`. -/
noncomputable def sim (V' : Strategy) (x z r : List Bool) : List Bool :=
  ((List.range (instanceVertexCount x)).findSome? fun t =>
    attemptStr V' x z (coinSlice (blockLen V' x.length) t r)).getD []

/-! ### An FP toolkit -/

/-- Polynomial-time computability transfers along pointwise equality. -/
private theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- Bitwise exclusive-or of a word with itself is the all-`false` word of its length. -/
theorem zipWith_xor_self (l : List Bool) : List.zipWith xor l l = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.replicate_succ]

/-- `w ↦ 0^{|w|}` is polynomial-time (`Complexity.polyTimeComputable_pairXor` on `⟨w, w⟩`). -/
theorem zeros_poly : PolyTimeComputable fun w => List.replicate w.length false :=
  ptc_congr (polyTimeComputable_pairXor.comp (polyTimeComputable_id.pairEncode polyTimeComputable_id))
    fun w => by simp

/-- The graph word `w` padded with `false` (or cut) to length `n²`: it decodes on `n`
vertices to the same graph as `w` and its length determines `n`. -/
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

/-- Padding to the square of a unary count is polynomial-time: on `⟨u, w⟩`, `padSq |u| w`
(`Complexity.polyTimeComputable_pairTakePoly` at `n²` on `⟨u, w ++ 0^{|u|²}⟩`). -/
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

/-- `decGraph` of a word whose length has square root `n` is `⟨n, decGraphAt n w⟩`. -/
theorem decGraph_eq_of_sqrt {w : List Bool} {n : ℕ} (h : Nat.sqrt w.length = n) :
    decGraph w = ⟨n, decGraphAt n w⟩ := by
  subst h
  rfl

/-- Relabelling a graph decoded on a given vertex count is polynomial-time: on
`⟨u, ⟨w, p⟩⟩` with `n = |u|`, the word `encGraph (permGraph (decGraphAt n w) (decPerm n p))`
(`polyTimeComputable_encPermGraph` on the padded word `padSq n w`). -/
theorem encPermGraphAt_poly : PolyTimeComputable fun z =>
    encGraph (permGraph (decGraphAt (pairFstD z).length (pairFstD (pairSndD z)))
      (decPerm (pairFstD z).length (pairSndD (pairSndD z)))) := by
  have hpad : PolyTimeComputable fun z => padSq (pairFstD z).length (pairFstD (pairSndD z)) :=
    ptc_congr (padSq_poly.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))) fun z => by simp
  have h := polyTimeComputable_encPermGraph.comp
    (hpad.pairEncode (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  refine ptc_congr h fun z => ?_
  simp only [Function.comp_apply]
  rw [pairFstD_pairEncode, pairSndD_pairEncode, decGraph_eq_of_sqrt (sqrt_length_padSq _ _)]
  simp only [decGraphAt_padSq]

/-! ### The simulator's machine layout -/

/-- The common input of the simulator's machine input `⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩`. -/
def simX (w : List Bool) : List Bool := pairFstD (NUPPT.inArg w)

/-- The auxiliary input of the simulator's machine input. -/
def simZ (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

/-- The coins of the simulator's machine input. -/
def simR (w : List Bool) : List Bool := NUPPT.inCoins w

/-- The common-input projection is polynomial-time. -/
theorem simX_poly : PolyTimeComputable simX :=
  polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg

/-- The auxiliary-input projection is polynomial-time. -/
theorem simZ_poly : PolyTimeComputable simZ :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-- The coin projection is polynomial-time. -/
theorem simR_poly : PolyTimeComputable simR := NUPPT.polyTimeComputable_inCoins

/-- The success flag of an optional value `if c then some v else none` is `decide c`. -/
private theorem isSome_ite_some_none {α : Type*} (c : Prop) [Decidable c] (v : α) :
    [(if c then some v else none).isSome] = [decide c] := by
  by_cases h : c <;> simp [h]

/-- The default of an optional value `if c then some v else none` is `if c then v else d`. -/
private theorem getD_ite_some_none {α : Type*} (c : Prop) [Decidable c] (v d : α) :
    (if c then some v else none).getD d = if c then v else d := by
  by_cases h : c <;> simp [h]

/-- The attempt of the simulator at index `t` on the layout `w`. -/
noncomputable def attemptAt (V' : Strategy) (w : List Bool) (t : ℕ) : Option (List Bool) :=
  attemptStr V' (simX w) (simZ w) (coinSlice (blockLen V' (simX w).length) t (simR w))

/-- **One attempt is polynomial-time.** On the indexed layout `u = ⟨1^t, w⟩`, both the
success test of the `t`-th attempt and its (defaulted) view are polynomial-time functions.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with `V'.next x z rV [H] =
A.output ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, ⟨H, []⟩⟩⟩, []⟩, rV⟩` (`Strategy.ofNUPPT_next`,
`NUPPT.runAtL_eq_output_layout`), polynomial-time by `A.polyTimeComputable_output` and
`NUPPT.polyTimeComputable_layout`. The block is `(r.drop (t · L)).take L` with `L` in unary
(`unaryPoly_comp (blockPoly V')`, `unaryMul_poly`, `pairDropPoly`, `truncate_poly`); its
fields are the head bit (`headBit_poly`), the permutation coins (`tail_poly`, `truncate_poly`
at `(|x|+1)²`) and the tape (`pairDropPoly`); the permutation word is
`polyTimeComputable_encPermFromCoins` on `⟨fst x, coins⟩`, the graph `H` is
`encPermGraphAt_poly` on `⟨1^n, ⟨G_{b'}, encPerm π⟩⟩` (`decPerm_encPerm`), the comparison is
`polyTimeComputable_pairEq` on the two one-bit words, and the view is assembled by
`PolyTimeComputable.pairEncode`. -/
theorem attemptAt_poly (V' : Strategy) (hV' : V'.Efficient) :
    PolyTimeComputable (fun u => [(attemptAt V' (pairSndD u) (pairFstD u).length).isSome]) ∧
    PolyTimeComputable (fun u => (attemptAt V' (pairSndD u) (pairFstD u).length).getD []) := by
  obtain ⟨A, hA, -, hnext⟩ := hV'
  have hx : PolyTimeComputable fun u => simX (pairSndD u) := simX_poly.comp polyTimeComputable_pairSndD
  have hz : PolyTimeComputable fun u => simZ (pairSndD u) := simZ_poly.comp polyTimeComputable_pairSndD
  have hr : PolyTimeComputable fun u => simR (pairSndD u) := simR_poly.comp polyTimeComputable_pairSndD
  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  -- the block length in unary
  have hL : PolyTimeComputable fun u => List.replicate (blockLen V' (simX (pairSndD u)).length) true := by
    have := unaryPoly_comp (blockPoly V') hx
    simpa only [blockPoly_eval] using this
  -- the block `c = (r.drop (t L)).take L`
  have hdrop : PolyTimeComputable fun u =>
      (simR (pairSndD u)).drop ((pairFstD u).length * blockLen V' (simX (pairSndD u)).length) := by
    have := (polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hL).pairEncode hr)
    refine ptc_congr this fun u => ?_
    simp
  have hc : PolyTimeComputable fun u =>
      coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u)) :=
    truncate_poly hdrop hL
  -- the guessed bit
  have hb : PolyTimeComputable fun u =>
      [(coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false] :=
    headBit_poly.comp hc
  -- `(|x| + 1)²` in unary
  have hP : PolyTimeComputable fun u => List.replicate (((simX (pairSndD u)).length + 1) ^ 2) true := by
    have := unaryPoly_comp (.normal 1 2) hx
    simpa only [PolyExpr.eval_normal, one_mul] using this
  -- the permutation coins
  have hpc : PolyTimeComputable fun u =>
      ((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop 1).take
        (((simX (pairSndD u)).length + 1) ^ 2) := by
    have htail : PolyTimeComputable fun u =>
        (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop 1 := by
      have := tail_poly.comp hc
      simpa only [List.drop_one] using this
    exact truncate_poly htail hP
  -- the verifier's tape
  have hrV : PolyTimeComputable fun u =>
      (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2) := by
    have h1P : PolyTimeComputable fun u =>
        List.replicate (1 + ((simX (pairSndD u)).length + 1) ^ 2) true :=
      unaryAdd_poly (unaryConst_poly 1) hP
    have := (polyTimeComputable_pairDropPoly .var).comp (h1P.pairEncode hc)
    refine ptc_congr this fun u => ?_
    simp
  -- the vertex count in unary
  have hn : PolyTimeComputable fun u => List.replicate (instanceVertexCount (simX (pairSndD u))) true :=
    unarySqrt_poly (unaryLength_poly (polyTimeComputable_pairFstD.comp hx))
  -- the sampled permutation as a word
  have hπ : PolyTimeComputable fun u => encPerm (samplePerm (instanceVertexCount (simX (pairSndD u)))
      (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop 1).take
        (((simX (pairSndD u)).length + 1) ^ 2))) := by
    have := polyTimeComputable_encPermFromCoins.comp ((polyTimeComputable_pairFstD.comp hx).pairEncode hpc)
    refine ptc_congr this fun u => ?_
    simp only [Function.comp_apply]
    rw [pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  -- the guessed graph's word
  have hGb : PolyTimeComputable fun u =>
      if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false then pairSndD (simX (pairSndD u)) else pairFstD (simX (pairSndD u)) :=
    polyTimeComputable_ite hb (polyTimeComputable_pairSndD.comp hx) (polyTimeComputable_pairFstD.comp hx)
  -- the message `H`
  have hH : PolyTimeComputable fun u => encGraph (permGraph
      (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
      (samplePerm (instanceVertexCount (simX (pairSndD u)))
        (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
          1).take (((simX (pairSndD u)).length + 1) ^ 2)))) := by
    have := encPermGraphAt_poly.comp (hn.pairEncode (hGb.pairEncode hπ))
    refine ptc_congr this fun u => ?_
    simp only [Function.comp_apply]
    rw [pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, decPerm_encPerm]
    split_ifs <;> rfl
  -- the verifier's reply
  have hmsg : PolyTimeComputable fun u => V'.next (simX (pairSndD u)) (simZ (pairSndD u))
      ((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2))
      [encGraph (permGraph
        (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
          false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
        (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2))))] := by
    have hlay := NUPPT.polyTimeComputable_layout (polyTimeComputable_unary.comp hx)
      ((hx.pairEncode hz).pairEncode (hH.pairEncode (polyTimeComputable_const [])))
      (polyTimeComputable_const []) hrV
    have := A.polyTimeComputable_output.comp hlay
    have hadv : ∀ k, A.advice k = [] := hA
    refine ptc_congr this fun u => ?_
    rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hadv]
    rfl
  -- the success test
  have htest : PolyTimeComputable fun u => [decide ((V'.next (simX (pairSndD u)) (simZ (pairSndD u))
      ((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2))
      [encGraph (permGraph
        (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
          false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
        (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2))))]).headD false =
      (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false)] := by
    have := polyTimeComputable_pairEq.comp ((headBit_poly.comp hmsg).pairEncode hb)
    refine ptc_congr this fun u => ?_
    simp
  -- the view
  have hview : PolyTimeComputable fun u => View.encode ⟨simX (pairSndD u), simZ (pairSndD u),
      (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2),
      [encGraph (permGraph
        (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
          false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
        (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2)))),
        encPerm (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2)))]⟩ :=
    ptc_congr ((hx.pairEncode hz).pairEncode (hrV.pairEncode (hH.pairEncode
      (hπ.pairEncode (polyTimeComputable_const []))))) fun u => rfl
  refine ⟨?_, ?_⟩
  · refine ptc_congr htest fun u => ?_
    simp only [attemptAt, attemptStr]
    exact isSome_ite_some_none _ _
  · refine ptc_congr (polyTimeComputable_ite htest hview (polyTimeComputable_const [])) fun u => ?_
    simp only [attemptAt, attemptStr, decide_eq_true_eq]
    exact getD_ite_some_none _ _ _

/-! ### The loop over the attempts -/

/-- `List.findSome?` over `List.range m` returns the value at the least accepted index
(`List.range_add`, `List.range_succ`, `List.findSome?_append`). -/
theorem findSome?_range_eq_of {β : Type*} (f : ℕ → Option β) {m i : ℕ} (hi : i < m) {v : β}
    (hv : f i = some v) (hmin : ∀ j < i, f j = none) : (List.range m).findSome? f = some v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = i + 1 + k := ⟨m - (i + 1), by omega⟩
  rw [List.range_add, List.findSome?_append, List.range_succ, List.findSome?_append]
  have h0 : (List.range i).findSome? f = none :=
    List.findSome?_eq_none_iff.2 fun j hj => hmin j (List.mem_range.1 hj)
  rw [h0]
  simp [hv]

/-- The defaulted `List.findSome?` over `List.range m` through the first accepted index
`EncodingMachines.firstIdx`: the value there if the search succeeds, `[]` otherwise.

**Proof sketch.** If `firstIdx q m < m` then `f` is `some` there (`q_firstIdx`) and `none`
below (`firstIdx_min`), so `findSome?_range_eq_of` applies; otherwise `firstIdx q m = m` and
`f` is `none` on the whole range (`firstIdx_eq_iff`, `List.findSome?_eq_none_iff`). -/
theorem findSome?_range_getD (f : ℕ → Option (List Bool)) (m : ℕ) :
    ((List.range m).findSome? f).getD [] =
      if firstIdx (fun t => (f t).isSome) m < m then (f (firstIdx (fun t => (f t).isSome) m)).getD []
      else [] := by
  split_ifs with h
  · have hq := q_firstIdx h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hq
    rw [findSome?_range_eq_of f h hv fun j hj => ?_, hv]
    have := firstIdx_min hj
    cases hf : f j
    · rfl
    · rw [hf] at this
      simp at this
  · have hm : firstIdx (fun t => (f t).isSome) m = m := le_antisymm firstIdx_le (not_lt.1 h)
    have hall := firstIdx_eq_iff.1 hm
    rw [List.findSome?_eq_none_iff.2 fun j hj => ?_]
    · rfl
    · have := hall j (List.mem_range.1 hj)
      cases hf : f j
      · rfl
      · rw [hf] at this
        simp at this

/-- **The simulator is polynomial-time** as a function of its machine layout: the first
accepted attempt index is `EncodingMachines.polyTimeComputable_firstIdx` with the success test
of `attemptAt_poly`, and the output is that attempt's view (`attemptAt_poly`) or `[]`
(`findSome?_range_getD`). -/
theorem sim_poly (V' : Strategy) (hV' : V'.Efficient) :
    PolyTimeComputable fun w => sim V' (simX w) (simZ w) (simR w) := by
  obtain ⟨hp, hout⟩ := attemptAt_poly V' hV'
  have hlen : PolyTimeComputable fun w => List.replicate (instanceVertexCount (simX w)) true :=
    unarySqrt_poly (unaryLength_poly (polyTimeComputable_pairFstD.comp simX_poly))
  have hidx := polyTimeComputable_firstIdx (p := fun w t => (attemptAt V' w t).isSome) hp hlen
  have hsel : PolyTimeComputable fun w =>
      (attemptAt V' w (firstIdx (fun t => (attemptAt V' w t).isSome) (instanceVertexCount (simX w)))).getD [] := by
    have := hout.comp (hidx.pairEncode polyTimeComputable_id)
    refine ptc_congr this fun w => ?_
    simp
  have hF := polyTimeComputable_ite (ltTest_poly hidx hlen) hsel (polyTimeComputable_const [])
  refine ptc_congr hF fun w => ?_
  simp only [decide_eq_true_eq]
  exact findSome?_range_getD (attemptAt V' w) (instanceVertexCount (simX w))

/-- **The simulator is a uniform PPT** (Claim-123.d, shadow form): `NUPPT.ofPolyTimeUniform`
of `sim_poly` with the coin polynomial `simCoins V'` computes `sim V' x z r` on
`⟨x, z⟩` at parameter `|x|` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_simulator (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = simCoins V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = sim V' x z (List.ofFn r) := by
  have hF := sim_poly V' hV'
  refine ⟨NUPPT.ofPolyTimeUniform hF (simCoins V'), NUPPT.ofPolyTimeUniform_uniform _ _, rfl, ?_⟩
  intro x z r
  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [simX, simZ, simR, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

end TCSlib.Cryptography.GIZK
