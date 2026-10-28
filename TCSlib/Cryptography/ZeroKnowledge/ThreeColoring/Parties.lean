/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the honest parties as string functions

The honest parties of [PS10, Protocol 127.5] as polynomial-time functions of the interactive
machine layout `⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`ColMachines.ilayout`), assembled from the
numeric models of `ThreeColoring/Machines.lean` and the unary FP toolkit of
`ZeroKnowledge/EncodingMachines.lean` (inventory item Inf-4.2 for Protocol 127.5):

* the one-iteration prover `proverStr` (commitment vector `commitStr`, opening `openStr`), the
  one-iteration verifier `verifierStr` (challenge `eOf`, check `checkStr`, verdict `verdictStr`),
  and the parties of the `n|E|`-fold protocol `proverRepStr`, `verifierRepStr`;
* their polynomial-time proofs (`proverStr_poly`, `verifierStr_poly`, `proverRepStr_poly`,
  `verifierRepStr_poly`), every number travelling in unary;
* the **layout lemmas** (`nOf_ilayout`, `mOf_ilayout`, `eOf_ilayout`, `commitStr_ilayout`,
  `openStr_ilayout`, …) that read the string functions on a layout `ilayout x z hist r` back
  as the typed operations of the strategies (`multiCom`, `samplePerm3`, `decColoring`,
  `sampleEdgeIdx`, `edgeOf`), which is what `ThreeColoring/ProtocolProofs.lean` uses to identify
  them with the next-message functions of `Protocol.lean`.

## Main results

* `TCSlib.Cryptography.ColMachines.proverStr_poly`, `ColMachines.verifierStr_poly`,
  `ColMachines.proverRepStr_poly`, `ColMachines.verifierRepStr_poly` — the parties are
  polynomial-time when `Com` is.
* `TCSlib.Cryptography.ColMachines.commitStr_ilayout`, `ColMachines.openStr_ilayout`,
  `ColMachines.eOf_ilayout`, `ColMachines.eRep_ilayout` — the layout lemmas.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### The honest parties as string functions -/

/-- Applying an index-parametrised polynomial-time function (polynomial-time in `⟨1^i, w⟩`) at
a unary index `f w` is polynomial-time. -/
theorem ptc_apply_unary {F : List Bool → ℕ → List Bool}
    (hF : PolyTimeComputable fun v => F (pairSndD v) (pairFstD v).length)
    {f : List Bool → ℕ} (hf : PolyTimeComputable fun w => List.replicate (f w) true) :
    PolyTimeComputable fun w => F w (f w) :=
  ptc_congr (hF.comp (hf.pairEncode polyTimeComputable_id)) fun w => by simp

/-- The second component of a word is no longer than the word. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length :=
  (Nat.le_add_left _ _).trans (length_pairFstD_add_pairSndD_le z)

/-- The common input of a layout is no longer than the layout. -/
theorem length_argX_le (w : List Bool) : (argX w).length ≤ w.length :=
  (length_pairFstD_le _).trans ((length_pairFstD_le _).trans ((length_pairSndD_le _).trans
    ((length_pairFstD_le _).trans (length_pairFstD_le _))))

section Parties

variable (Com : List Bool → List Bool) (ℓ : PolyExpr)

/-- The vertex count `n = √|x|` read off the layout. -/
def nOf (w : List Bool) : ℕ := Nat.sqrt (argX w).length

/-- The randomness length `ℓ(n)` of the commitments. -/
def LOf (w : List Bool) : ℕ := ℓ.eval (nOf w)

/-- The number of (ordered) edges `|E| = countTrue x n²` read off the layout. -/
def mOf (w : List Bool) : ℕ := countTrue (argX w) (nOf w * nOf w)

/-- The prover's colour permutation as a table: the sampler on the first `3|x|` coins. -/
noncomputable def tblOf (w : List Bool) : List Bool :=
  tableOfIdx (sampleVal ((NUPPT.inCoins w).take (3 * (argX w).length)) 6 3 (argX w).length 6)

/-- The encoding of the permuted colour of vertex `i`. -/
noncomputable def colBits (w : List Bool) (i : ℕ) : List Bool :=
  colorFromTable (tblOf w) (colorVal (argZ w) i)

/-- The randomness block of vertex `i`: `ℓ(n)` coins after the first `3|x| + i ℓ(n)`. -/
def blk (w : List Bool) (i : ℕ) : List Bool :=
  padTo (LOf ℓ w) ((NUPPT.inCoins w).drop (3 * (argX w).length + i * LOf ℓ w))

/-- The commitment to the permuted colour of vertex `i`. -/
noncomputable def comAt (w : List Bool) (i : ℕ) : List Bool :=
  Com (pairEncode (padTo (nOf w) (colBits w i)) (blk ℓ w i))

/-- The prover's first message: the encoded list of the `n` commitments. -/
noncomputable def commitStr (w : List Bool) : List Bool :=
  (List.range (nOf w)).flatMap fun i => pairEncode (comAt Com ℓ w i) []

/-- The prover's opening of the edge named by the challenge (first received message). -/
noncomputable def openStr (w : List Bool) : List Bool :=
  let e := (pairFstD (argM w)).length % mOf w
  let j := nthTrue (argX w) (nOf w * nOf w) e
  pairEncode (pairEncode (colBits w (j / nOf w)) (blk ℓ w (j / nOf w)))
    (pairEncode (colBits w (j % nOf w)) (blk ℓ w (j % nOf w)))

/-- The honest prover of one iteration as a function of the layout. -/
noncomputable def proverStr (w : List Bool) : List Bool :=
  if argM w = [] then commitStr Com ℓ w else if mOf w = 0 then [] else openStr ℓ w

/-- The vertex count is polynomial-time in unary. -/
theorem nOf_poly : PolyTimeComputable fun w => List.replicate (nOf w) true :=
  unarySqrt_poly (unaryLength_poly argX_poly)

/-- The randomness length is polynomial-time in unary. -/
theorem LOf_poly : PolyTimeComputable fun w => List.replicate (LOf ℓ w) true :=
  unaryPolyOf_poly ℓ nOf_poly

/-- The edge count is polynomial-time in unary. -/
theorem mOf_poly : PolyTimeComputable fun w => List.replicate (mOf w) true :=
  countTrue_poly argX_poly (unaryMul_poly nOf_poly nOf_poly)

/-- The permutation table is polynomial-time. -/
theorem tblOf_poly : PolyTimeComputable tblOf := by
  have hr : PolyTimeComputable fun w => (NUPPT.inCoins w).take (3 * (argX w).length) :=
    ptc_congr ((polyTimeComputable_pairTakePoly (.mul (.const 3) .var)).comp
      (argX_poly.pairEncode NUPPT.polyTimeComputable_inCoins)) fun w => by simp
  exact tableOfIdx_poly (sampleVal_poly hr (unaryConst_poly 6) (unaryConst_poly 3)
    (unaryLength_poly argX_poly) (unaryConst_poly 6) (.const 8) fun _ => by simp)

/-- The permuted colour bits are polynomial-time in `⟨1^i, w⟩`. -/
theorem colBits_poly : PolyTimeComputable fun v => colBits (pairSndD v) (pairFstD v).length :=
  colorFromTable_poly (tblOf_poly.comp polyTimeComputable_pairSndD)
    (colorVal_poly (argZ_poly.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))

/-- The randomness blocks are polynomial-time in `⟨1^i, w⟩`. -/
theorem blk_poly : PolyTimeComputable fun v => blk ℓ (pairSndD v) (pairFstD v).length := by
  have hb : PolyTimeComputable fun v => List.replicate
      (3 * (argX (pairSndD v)).length + (pairFstD v).length * LOf ℓ (pairSndD v)) true :=
    unaryAdd_poly
      (unaryMul_poly (unaryConst_poly 3) (unaryLength_poly (argX_poly.comp polyTimeComputable_pairSndD)))
      (unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD)
        ((LOf_poly ℓ).comp polyTimeComputable_pairSndD))
  have hdrop : PolyTimeComputable fun v => (NUPPT.inCoins (pairSndD v)).drop
      (3 * (argX (pairSndD v)).length + (pairFstD v).length * LOf ℓ (pairSndD v)) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      (hb.pairEncode (NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD)))
      fun v => by simp
  exact padTo_poly hdrop ((LOf_poly ℓ).comp polyTimeComputable_pairSndD)

/-- The commitments are polynomial-time in `⟨1^i, w⟩` when `Com` is. -/
theorem comAt_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun v => comAt Com ℓ (pairSndD v) (pairFstD v).length :=
  hCom.comp ((padTo_poly colBits_poly (nOf_poly.comp polyTimeComputable_pairSndD)).pairEncode
    (blk_poly ℓ))

/-- The prover's first message is polynomial-time (`polyTimeComputable_flatMap_range`). -/
theorem commitStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (commitStr Com ℓ) :=
  polyTimeComputable_flatMap_range (E := fun w i => pairEncode (comAt Com ℓ w i) [])
    ((comAt_poly Com ℓ hCom).pairEncode (polyTimeComputable_const [])) nOf_poly

/-- The prover's opening is polynomial-time. -/
theorem openStr_poly : PolyTimeComputable (openStr ℓ) := by
  have he : PolyTimeComputable fun w => List.replicate ((pairFstD (argM w)).length % mOf w) true := by
    simpa only [modNum_eq] using
      modNum_poly (unaryLength_poly (polyTimeComputable_pairFstD.comp argM_poly)) mOf_poly
  have hj := nthTrue_poly argX_poly (unaryMul_poly nOf_poly nOf_poly) he
  have hu : PolyTimeComputable fun w => List.replicate
      (nthTrue (argX w) (nOf w * nOf w) ((pairFstD (argM w)).length % mOf w) / nOf w) true := by
    simpa only [divNum_eq] using divNum_poly hj nOf_poly
  have hv : PolyTimeComputable fun w => List.replicate
      (nthTrue (argX w) (nOf w * nOf w) ((pairFstD (argM w)).length % mOf w) % nOf w) true := by
    simpa only [modNum_eq] using modNum_poly hj nOf_poly
  exact ((ptc_apply_unary colBits_poly hu).pairEncode (ptc_apply_unary (blk_poly ℓ) hu)).pairEncode
    ((ptc_apply_unary colBits_poly hv).pairEncode (ptc_apply_unary (blk_poly ℓ) hv))

/-- The honest prover of one iteration is polynomial-time when `Com` is. -/
theorem proverStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (proverStr Com ℓ) := by
  have h := polyTimeComputable_ite (isNil_poly.comp argM_poly) (commitStr_poly Com ℓ hCom)
    (polyTimeComputable_ite (eqTest_poly mOf_poly (unaryConst_poly 0)) (polyTimeComputable_const [])
      (openStr_poly ℓ))
  exact ptc_congr h fun w => by simp only [proverStr, decide_eq_true_eq, Function.comp_apply]

/-- The verifier's challenge: the rejection-sampled edge index on its tape. -/
noncomputable def eOf (w : List Bool) : ℕ :=
  sampleVal (NUPPT.inCoins w) (mOf w) (Nat.size (mOf w)) (argX w).length 0

/-- The challenge is polynomial-time in unary (`2^{size |E|} ≤ 2|E| + 1 ≤ 2|w| + 1`). -/
theorem eOf_poly : PolyTimeComputable fun w => List.replicate (eOf w) true :=
  sampleVal_poly NUPPT.polyTimeComputable_inCoins mOf_poly (unarySize_poly mOf_poly)
    (unaryLength_poly argX_poly) (unaryConst_poly 0) (.add (.mul (.const 2) .var) (.const 1))
    fun w => by
      have h1 := two_pow_size_le_two_mul_succ (mOf w)
      have h2 : mOf w ≤ w.length :=
        (countTrue_le _ _).trans ((Nat.sqrt_le _).trans (length_argX_le w))
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega

/-- The verifier's check of one iteration on the words `x`, `com`, `opn`, the challenge `e`, the
randomness length `L`, the vertex count `n` and the edge count `m`: the openings have randomness
of length `L`, both match the commitments at the endpoints of the `(e mod m)`-th edge, and the
two colours differ. -/
noncomputable def checkStr (L n m : ℕ) (x com opn : List Bool) (e : ℕ) : Bool :=
  let j := nthTrue x (n * n) (e % m)
  let a := colorVal (pairFstD (pairFstD opn)) 0
  let ri := pairSndD (pairFstD opn)
  let b := colorVal (pairFstD (pairSndD opn)) 0
  let rj := pairSndD (pairSndD opn)
  decide (ri.length = L ∧ rj.length = L ∧
    Com (pairEncode (padTo n (encColorOfVal a)) ri) = pairFstD (pairSndD^[j / n] com) ∧
    Com (pairEncode (padTo n (encColorOfVal b)) rj) = pairFstD (pairSndD^[j % n] com) ∧ a ≠ b)

/-- The check is polynomial-time in its (polynomial-time, unary) components. -/
theorem checkStr_poly (hCom : PolyTimeComputable Com)
    {L n m : List Bool → ℕ} (hL : PolyTimeComputable fun w => List.replicate (L w) true)
    (hn : PolyTimeComputable fun w => List.replicate (n w) true)
    (hm : PolyTimeComputable fun w => List.replicate (m w) true)
    {x com opn : List Bool → List Bool} (hx : PolyTimeComputable x) (hcom : PolyTimeComputable com)
    (hopn : PolyTimeComputable opn)
    {e : List Bool → ℕ} (he : PolyTimeComputable fun w => List.replicate (e w) true) :
    PolyTimeComputable fun w => [checkStr Com (L w) (n w) (m w) (x w) (com w) (opn w) (e w)] := by
  have hem : PolyTimeComputable fun w => List.replicate (e w % m w) true := by
    simpa only [modNum_eq] using modNum_poly he hm
  have hj := nthTrue_poly hx (unaryMul_poly hn hn) hem
  have hu : PolyTimeComputable fun w =>
      List.replicate (nthTrue (x w) (n w * n w) (e w % m w) / n w) true := by
    simpa only [divNum_eq] using divNum_poly hj hn
  have hv : PolyTimeComputable fun w =>
      List.replicate (nthTrue (x w) (n w * n w) (e w % m w) % n w) true := by
    simpa only [modNum_eq] using modNum_poly hj hn
  have ha := colorVal_poly (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp hopn))
    (unaryConst_poly 0)
  have hb := colorVal_poly (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hopn))
    (unaryConst_poly 0)
  have hri := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hopn)
  have hrj := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hopn)
  have t1 := eqTest_poly (unaryLength_poly hri) hL
  have t2 := eqTest_poly (unaryLength_poly hrj) hL
  have t3 := polyTimeComputable_pairEq.comp
    ((hCom.comp ((padTo_poly (encColorOfVal_poly ha) hn).pairEncode hri)).pairEncode
      (polyTimeComputable_pairFstD.comp (iterSnd_poly hcom hu)))
  have t4 := polyTimeComputable_pairEq.comp
    ((hCom.comp ((padTo_poly (encColorOfVal_poly hb) hn).pairEncode hrj)).pairEncode
      (polyTimeComputable_pairFstD.comp (iterSnd_poly hcom hv)))
  have t5 := not_poly (eqTest_poly ha hb)
  have h := polyTimeComputable_and t1 (polyTimeComputable_and t2
    (polyTimeComputable_and t3 (polyTimeComputable_and t4 t5)))
  convert h using 1
  funext w
  simp only [checkStr, Bool.decide_and, decide_not, pairFstD_pairEncode, pairSndD_pairEncode,
    Function.comp_apply]

/-- The verifier's verdict: well-formedness, and either no edges or `n ≥ 2` with the check. -/
noncomputable def verdictStr (w : List Bool) : Bool :=
  decide (argX w = (argX w).take (nOf w * nOf w)) &&
    (decide (mOf w = 0) || (decide (2 ≤ nOf w) &&
      checkStr Com (LOf ℓ w) (nOf w) (mOf w) (argX w) (pairFstD (argM w))
        (pairFstD (pairSndD (argM w))) (eOf w)))

/-- The verdict is polynomial-time when `Com` is. -/
theorem verdictStr_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun w => [verdictStr Com ℓ w] := by
  have hwf : PolyTimeComputable fun w => [decide (argX w = (argX w).take (nOf w * nOf w))] :=
    ptc_congr (polyTimeComputable_pairEq.comp
      (argX_poly.pairEncode (truncate_poly argX_poly (unaryMul_poly nOf_poly nOf_poly))))
      fun w => by simp
  exact polyTimeComputable_and hwf (or_poly (eqTest_poly mOf_poly (unaryConst_poly 0))
    (polyTimeComputable_and (leTest_poly (unaryConst_poly 2) nOf_poly)
      (checkStr_poly Com hCom (LOf_poly ℓ) nOf_poly mOf_poly argX_poly
        (polyTimeComputable_pairFstD.comp argM_poly)
        (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp argM_poly)) eOf_poly)))

/-- The verifier of one iteration as a function of the layout: `[false]` on the empty history,
the unary challenge after the commitments, the verdict after the openings, `[false]` later. -/
noncomputable def verifierStr (w : List Bool) : List Bool :=
  if argM w = [] then [false]
  else if pairSndD (argM w) = [] then List.replicate (eOf w) true
  else if pairSndD (pairSndD (argM w)) = [] then [verdictStr Com ℓ w]
  else [false]

/-- The verifier of one iteration is polynomial-time when `Com` is. -/
theorem verifierStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (verifierStr Com ℓ) := by
  have h := polyTimeComputable_ite (isNil_poly.comp argM_poly) (polyTimeComputable_const [false])
    (polyTimeComputable_ite (isNil_poly.comp (polyTimeComputable_pairSndD.comp argM_poly)) eOf_poly
      (polyTimeComputable_ite
        (isNil_poly.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp argM_poly)))
        (verdictStr_poly Com ℓ hCom) (polyTimeComputable_const [false])))
  exact ptc_congr h fun w => by simp only [verifierStr, decide_eq_true_eq, Function.comp_apply]

/-- The number of coins of one iteration of the prover at common-input length `N`:
`3N + N ℓ(N)`. -/
def proverCoinsOf (N : ℕ) : ℕ := 3 * N + N * ℓ.eval N

/-- The prover of the repeated protocol as a function of the layout: iteration
`t = |hist| / 2` runs the one-iteration prover on the `t`-th coin block and on the history
`[]` or `[last message]` according to the parity of `|hist|`. -/
noncomputable def proverRepStr (w : List Bool) : List Bool :=
  let h := histLen (argM w)
  let c := proverCoinsOf ℓ (argX w).length
  if h / 2 < nOf w * mOf w then
    proverStr Com ℓ (NUPPT.layout (List.replicate (argX w).length true)
      (pairEncode (pairEncode (argX w) (argZ w))
        (if h % 2 = 0 then [] else pairEncode (pairFstD (pairSndD^[h - 1] (argM w))) []))
      [] (((NUPPT.inCoins w).drop (h / 2 * c)).take c))
  else []

/-- The prover of the repeated protocol is polynomial-time when `Com` is. -/
theorem proverRepStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (proverRepStr Com ℓ) := by
  have hh := histLen_poly.comp argM_poly
  have ht : PolyTimeComputable fun w => List.replicate (histLen (argM w) / 2) true := by
    simpa only [divNum_eq] using divNum_poly hh (unaryConst_poly 2)
  have hpar : PolyTimeComputable fun w => [decide (histLen (argM w) % 2 = 0)] := by
    simpa only [modNum_eq] using eqTest_poly (modNum_poly hh (unaryConst_poly 2)) (unaryConst_poly 0)
  have hxl := unaryLength_poly argX_poly
  have hc : PolyTimeComputable fun w => List.replicate (proverCoinsOf ℓ (argX w).length) true :=
    unaryAdd_poly (unaryMul_poly (unaryConst_poly 3) hxl) (unaryMul_poly hxl (unaryPolyOf_poly ℓ hxl))
  have hdrop : PolyTimeComputable fun w =>
      (NUPPT.inCoins w).drop (histLen (argM w) / 2 * proverCoinsOf ℓ (argX w).length) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryMul_poly ht hc).pairEncode NUPPT.polyTimeComputable_inCoins)) fun w => by simp
  have hslice := truncate_poly hdrop hc
  have hlast : PolyTimeComputable fun w => pairFstD (pairSndD^[histLen (argM w) - 1] (argM w)) :=
    polyTimeComputable_pairFstD.comp (iterSnd_poly argM_poly (unarySub_poly hh (unaryConst_poly 1)))
  have hM := polyTimeComputable_ite hpar (polyTimeComputable_const [])
    (hlast.pairEncode (polyTimeComputable_const []))
  have hlay := NUPPT.polyTimeComputable_layout hxl ((argX_poly.pairEncode argZ_poly).pairEncode hM)
    (polyTimeComputable_const []) hslice
  have h := polyTimeComputable_ite (ltTest_poly ht (unaryMul_poly nOf_poly mOf_poly))
    (ptc_comp (proverStr_poly Com ℓ hCom) hlay) (polyTimeComputable_const [])
  exact ptc_congr h fun w => by simp only [proverRepStr, decide_eq_true_eq]

/-- The challenge of iteration `t` of the repeated verifier: the sampler on the `t`-th block of
`(|x| + 1)²` coins. -/
noncomputable def eRep (w : List Bool) (t : ℕ) : ℕ :=
  sampleVal (((NUPPT.inCoins w).drop (t * ((argX w).length + 1) ^ 2)).take (((argX w).length + 1) ^ 2))
    (mOf w) (Nat.size (mOf w)) (argX w).length 0

/-- The challenges of the repeated verifier are polynomial-time in `⟨1^t, w⟩`. -/
theorem eRep_poly : PolyTimeComputable fun v => List.replicate (eRep (pairSndD v) (pairFstD v).length) true := by
  have hB : PolyTimeComputable fun v => List.replicate (((argX (pairSndD v)).length + 1) ^ 2) true :=
    unaryPolyOf_poly (.pow (.add .var (.const 1)) 2)
      (unaryLength_poly (argX_poly.comp polyTimeComputable_pairSndD))
  have hdrop : PolyTimeComputable fun v => (NUPPT.inCoins (pairSndD v)).drop
      ((pairFstD v).length * ((argX (pairSndD v)).length + 1) ^ 2) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD) hB).pairEncode
        (NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD))) fun v => by simp
  have hm := mOf_poly.comp polyTimeComputable_pairSndD
  exact sampleVal_poly (truncate_poly hdrop hB) hm (unarySize_poly hm)
    (unaryLength_poly (argX_poly.comp polyTimeComputable_pairSndD)) (unaryConst_poly 0)
    (.add (.mul (.const 2) .var) (.const 1)) fun v => by
      have h1 := two_pow_size_le_two_mul_succ (mOf (pairSndD v))
      have h2 : mOf (pairSndD v) ≤ v.length :=
        (countTrue_le _ _).trans ((Nat.sqrt_le _).trans
          ((length_argX_le _).trans (length_pairSndD_le v)))
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega

/-- The check of iteration `t` of the repeated verifier on messages `2t`, `2t + 1`. -/
noncomputable def checkRep (w : List Bool) (t : ℕ) : Bool :=
  checkStr Com (LOf ℓ w) (nOf w) (mOf w) (argX w) (pairFstD (pairSndD^[2 * t] (argM w)))
    (pairFstD (pairSndD^[2 * t + 1] (argM w))) (eRep w t)

/-- The iteration checks are polynomial-time in `⟨1^t, w⟩` when `Com` is. -/
theorem checkRep_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun v => [checkRep Com ℓ (pairSndD v) (pairFstD v).length] := by
  have h2t := unaryMul_poly (unaryConst_poly 2) (unaryLength_poly polyTimeComputable_pairFstD)
  exact checkStr_poly Com hCom ((LOf_poly ℓ).comp polyTimeComputable_pairSndD)
    (nOf_poly.comp polyTimeComputable_pairSndD) (mOf_poly.comp polyTimeComputable_pairSndD)
    (argX_poly.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_pairFstD.comp (iterSnd_poly (argM_poly.comp polyTimeComputable_pairSndD) h2t))
    (polyTimeComputable_pairFstD.comp (iterSnd_poly (argM_poly.comp polyTimeComputable_pairSndD)
      (unaryAdd_poly h2t (unaryConst_poly 1))))
    eRep_poly

/-- The verdict of the repeated verifier: well-formedness, and either no edges or `n ≥ 2` with
every one of the `n|E|` iteration checks passing (no failing iteration below `n|E|`). -/
noncomputable def verdictRepStr (w : List Bool) : Bool :=
  decide (argX w = (argX w).take (nOf w * nOf w)) &&
    (decide (mOf w = 0) || (decide (2 ≤ nOf w) &&
      decide (firstIdx (fun t => !checkRep Com ℓ w t) (nOf w * mOf w) = nOf w * mOf w)))

/-- The repeated verdict is polynomial-time when `Com` is. -/
theorem verdictRepStr_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun w => [verdictRepStr Com ℓ w] := by
  have hwf : PolyTimeComputable fun w => [decide (argX w = (argX w).take (nOf w * nOf w))] :=
    ptc_congr (polyTimeComputable_pairEq.comp
      (argX_poly.pairEncode (truncate_poly argX_poly (unaryMul_poly nOf_poly nOf_poly))))
      fun w => by simp
  have hN := unaryMul_poly nOf_poly mOf_poly
  have hfirst := polyTimeComputable_firstIdx (p := fun w t => !checkRep Com ℓ w t)
    (not_poly (checkRep_poly Com ℓ hCom)) hN
  exact polyTimeComputable_and hwf (or_poly (eqTest_poly mOf_poly (unaryConst_poly 0))
    (polyTimeComputable_and (leTest_poly (unaryConst_poly 2) nOf_poly) (eqTest_poly hfirst hN)))

/-- The verifier of the repeated protocol as a function of the layout. -/
noncomputable def verifierRepStr (w : List Bool) : List Bool :=
  let h := histLen (argM w)
  if h % 2 = 1 then (if h / 2 < nOf w * mOf w then List.replicate (eRep w (h / 2)) true else [])
  else if h = 2 * ((argX w).length * (argX w).length) then [verdictRepStr Com ℓ w]
  else []

/-- The verifier of the repeated protocol is polynomial-time when `Com` is. -/
theorem verifierRepStr_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable (verifierRepStr Com ℓ) := by
  have hh := histLen_poly.comp argM_poly
  have ht : PolyTimeComputable fun w => List.replicate (histLen (argM w) / 2) true := by
    simpa only [divNum_eq] using divNum_poly hh (unaryConst_poly 2)
  have hpar : PolyTimeComputable fun w => [decide (histLen (argM w) % 2 = 1)] := by
    simpa only [modNum_eq] using eqTest_poly (modNum_poly hh (unaryConst_poly 2)) (unaryConst_poly 1)
  have hxl := unaryLength_poly argX_poly
  have hfull := eqTest_poly hh (unaryMul_poly (unaryConst_poly 2) (unaryMul_poly hxl hxl))
  have hchal := ptc_apply_unary (F := fun w t => List.replicate (eRep w t) true) eRep_poly ht
  have h := polyTimeComputable_ite hpar
    (polyTimeComputable_ite (ltTest_poly ht (unaryMul_poly nOf_poly mOf_poly)) hchal
      (polyTimeComputable_const []))
    (polyTimeComputable_ite hfull (verdictRepStr_poly Com ℓ hCom) (polyTimeComputable_const []))
  exact ptc_congr h fun w => by simp only [verifierRepStr, decide_eq_true_eq]

/-! ### The string functions on the interactive layout -/

section Layout

variable (x y z r : List Bool) (hist : List (List Bool))

/-- The vertex count read off a layout. -/
theorem nOf_ilayout : nOf (ilayout x z hist r) = (decGraph x).1 := by
  show Nat.sqrt (argX (ilayout x z hist r)).length = _
  rw [argX_ilayout]
  rfl

/-- The edge count read off a layout. -/
theorem mOf_ilayout : mOf (ilayout x z hist r) = edgeCount (decGraph x).2 := by
  show countTrue (argX (ilayout x z hist r)) (nOf (ilayout x z hist r) * nOf (ilayout x z hist r)) = _
  rw [argX_ilayout, nOf_ilayout, edgeCount_eq (decGraph x).2 x (decGraph_apply x)]

/-- The randomness length read off a layout. -/
theorem LOf_ilayout : LOf ℓ (ilayout x z hist r) = ℓ.eval (decGraph x).1 := by
  show ℓ.eval (nOf (ilayout x z hist r)) = _
  rw [nOf_ilayout]

/-- The verifier's challenge read off a layout is the edge sampler on its tape. -/
theorem eOf_ilayout :
    eOf (ilayout x z hist r) = sampleEdgeIdx (edgeCount (decGraph x).2) x.length r := by
  show sampleVal (NUPPT.inCoins (ilayout x z hist r)) (mOf (ilayout x z hist r))
    (Nat.size (mOf (ilayout x z hist r))) (argX (ilayout x z hist r)).length 0 = _
  rw [inCoins_ilayout, mOf_ilayout, argX_ilayout, sampleEdgeIdx, map_val_sampleIdx_getD]

/-- The challenge of iteration `t` of the repeated verifier read off a layout. -/
theorem eRep_ilayout (t : ℕ) : eRep (ilayout x z hist r) t =
    sampleEdgeIdx (edgeCount (decGraph x).2) x.length
      ((r.drop (t * (x.length + 1) ^ 2)).take ((x.length + 1) ^ 2)) := by
  show sampleVal (((NUPPT.inCoins (ilayout x z hist r)).drop
      (t * ((argX (ilayout x z hist r)).length + 1) ^ 2)).take
        (((argX (ilayout x z hist r)).length + 1) ^ 2))
    (mOf (ilayout x z hist r)) (Nat.size (mOf (ilayout x z hist r)))
    (argX (ilayout x z hist r)).length 0 = _
  rw [inCoins_ilayout, mOf_ilayout, argX_ilayout, sampleEdgeIdx, map_val_sampleIdx_getD]

/-- The permutation table read off a layout is the table of the sampled permutation. -/
theorem tblOf_ilayout :
    tblOf (ilayout x z hist r) = permTable (samplePerm3 x.length (r.take (3 * x.length))) := by
  show tableOfIdx (sampleVal ((NUPPT.inCoins (ilayout x z hist r)).take
    (3 * (argX (ilayout x z hist r)).length)) 6 3 (argX (ilayout x z hist r)).length 6) = _
  rw [inCoins_ilayout, argX_ilayout, permTable_samplePerm3]

/-- The permuted colour bits of vertex `i` read off a layout. -/
theorem colBits_ilayout (i : Fin (decGraph x).1) :
    colBits (ilayout x y hist r) i =
      encColor (samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i)) := by
  show colorFromTable (tblOf (ilayout x y hist r)) (colorVal (argZ (ilayout x y hist r)) i) = _
  rw [tblOf_ilayout, argZ_ilayout, ← decColoring_val, colorFromTable_permTable]

/-- The randomness block of vertex `i` read off a layout. -/
theorem blk_ilayout (i : Fin (decGraph x).1) :
    blk ℓ (ilayout x y hist r) i = List.ofFn (fun j : Fin (ℓ.eval (decGraph x).1) =>
      r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) := by
  show padTo (LOf ℓ (ilayout x y hist r)) ((NUPPT.inCoins (ilayout x y hist r)).drop
    (3 * (argX (ilayout x y hist r)).length + i * LOf ℓ (ilayout x y hist r))) = _
  rw [LOf_ilayout, inCoins_ilayout, argX_ilayout, ofFn_getD_add]

/-- The commitment of vertex `k` read off a layout. -/
theorem comAt_ilayout (k : ℕ) (hk : k < (decGraph x).1) :
    comAt Com ℓ (ilayout x y hist r) k = Com (pairEncode
      (List.ofFn (padColor (decGraph x).1 (samplePerm3 x.length (r.take (3 * x.length))
        (decColoring (decGraph x).1 y ⟨k, hk⟩))))
      (List.ofFn (fun j : Fin (ℓ.eval (decGraph x).1) =>
        r.getD (3 * x.length + k * ℓ.eval (decGraph x).1 + j) false))) := by
  show Com (pairEncode (padTo (nOf (ilayout x y hist r)) (colBits (ilayout x y hist r) k))
    (blk ℓ (ilayout x y hist r) k)) = _
  rw [nOf_ilayout,
    show colBits (ilayout x y hist r) k = colBits (ilayout x y hist r) ↑(⟨k, hk⟩ : Fin _) from rfl,
    colBits_ilayout,
    show blk ℓ (ilayout x y hist r) k = blk ℓ (ilayout x y hist r) ↑(⟨k, hk⟩ : Fin _) from rfl,
    blk_ilayout, padColor, ofFn_padFin]

/-- The prover's first message read off a layout is the commitment vector `multiCom`. -/
theorem commitStr_ilayout :
    commitStr Com ℓ (ilayout x y hist r) = multiCom Com
      (fun i => padColor (decGraph x).1 (samplePerm3 x.length (r.take (3 * x.length))
        (decColoring (decGraph x).1 y i)))
      (fun (i : Fin (decGraph x).1) (j : Fin (ℓ.eval (decGraph x).1)) =>
        r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) := by
  show (List.range (nOf (ilayout x y hist r))).flatMap
    (fun i => pairEncode (comAt Com ℓ (ilayout x y hist r) i) []) = _
  rw [nOf_ilayout, multiCom,
    encodeMsgs_ofFn_eq_flatMap _ (fun i => comAt Com ℓ (ilayout x y hist r) i)]
  intro k hk
  rw [comAt_ilayout Com ℓ x y r hist k hk]

/-- The prover's opening read off a layout (first received message `w`, at least one edge). -/
theorem openStr_ilayout (w : List Bool) (hm : 0 < edgeCount (decGraph x).2) :
    openStr ℓ (ilayout x y (w :: hist) r) =
      let p := edgeOf (decGraph x).2 ⟨w.length % edgeCount (decGraph x).2, Nat.mod_lt _ hm⟩
      let c' := fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i)
      let rr := fun (i : Fin (decGraph x).1) (j : Fin (ℓ.eval (decGraph x).1)) =>
        r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false
      pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (rr p.1)))
        (pairEncode (encColor (c' p.2)) (List.ofFn (rr p.2))) := by
  obtain ⟨h1, h2⟩ := edgeOf_val (decGraph x).2 x (decGraph_apply x)
    ⟨w.length % edgeCount (decGraph x).2, Nat.mod_lt _ hm⟩
  show pairEncode (pairEncode (colBits (ilayout x y (w :: hist) r) _)
      (blk ℓ (ilayout x y (w :: hist) r) _))
    (pairEncode (colBits (ilayout x y (w :: hist) r) _) (blk ℓ (ilayout x y (w :: hist) r) _)) = _
  simp only [argM_ilayout, Strategy.encodeMsgs_cons, pairFstD_pairEncode, mOf_ilayout, nOf_ilayout,
    argX_ilayout]
  rw [← h1, ← h2, colBits_ilayout, colBits_ilayout, blk_ilayout, blk_ilayout]

end Layout

end Parties

end TCSlib.Cryptography.ColMachines
