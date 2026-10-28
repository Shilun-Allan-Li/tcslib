/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorNumeric
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The 3-colouring simulator as a polynomial-time machine

The machine behind Claim-128.a of `ThreeColoring/Simulator.lean` (`exists_colSimulator`): the
string-level simulator of [PS10, Algorithm 128.7], truncated at `n|E|` attempts (D8), is a
polynomial-time function of its machine layout `⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩`, hence a uniform
`Complexity.NUPPT`. The shadows of the frozen string definitions and the numeric form
`attemptNum` of one attempt are in `ThreeColoring/SimulatorNumeric.lean`; this file proves each
ingredient of `attemptNum` polynomial-time in unary with the toolkit of
`EncodingMachines.lean` (bit counting, finite tables, the rejection sampler through
`EncodingPermutations.trialIdx_poly`, a loop emitting a computed number of chunks) and
assembles one attempt (`attemptAt_poly`) and the loop over the attempts (`sim_poly`, through
`EncodingMachines.polyTimeComputable_firstIdx`).

## Main definitions

* `TCSlib.Cryptography.ColSimMachine.simX`, `simZ`, `simR`, `attemptAt` — the projections of
  the simulator's layout and the attempt at a given index on it.

## Main results

* `TCSlib.Cryptography.ColSimMachine.countBits_poly`, `table_poly`, `sampleNum_poly`,
  `emitLoop_poly` — the generic machine helpers.
* `TCSlib.Cryptography.ColSimMachine.attemptNum_poly`, `attemptAt_poly` — one attempt is
  polynomial-time.
* `TCSlib.Cryptography.ColSimMachine.sim_poly` — the simulator is a polynomial-time function
  of its layout.
* `TCSlib.Cryptography.ColSimMachine.exists_simulator` — the simulator is a uniform PPT
  (Claim-128.a, shadow form).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7 Algorithm 128.7, p. 128.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColSimMachine

open Complexity Turing Complexity.StateLoop EncodingMachines

/-! ### Generic machine helpers -/

/-- Polynomial-time computability transfers along pointwise equality. -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- One more position adds the bit at that position to the count. -/
theorem countBits_succ (x : List Bool) (k : ℕ) :
    countBits x (k + 1) = countBits x k + (x.getD k false).toNat := by
  unfold countBits
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton]
  cases x.getD k false <;> simp

/-- The count of set bits is at most the number of positions. -/
theorem countBits_le (x : List Bool) (k : ℕ) : countBits x k ≤ k := by
  unfold countBits
  exact (List.length_filter_le _ _).trans (by simp)

/-- **Counting set bits is unary polynomial-time**: `z ↦ 1^{countBits (X z) (K z)}` for a
polynomial-time word `X` and a unary bound `K`.

**Proof sketch.** A counted loop (`EncodingMachines.polyTimeComputable_loopState`) of `K z`
rounds from `[]` whose round `i` appends a token iff bit `i` of `X z` is set
(`EncodingMachines.getBit_poly`), truncated to `K z` tokens so that every update is bounded; on
the genuine orbit the truncation is the identity (`countBits_le`, `countBits_succ`). -/
theorem countBits_poly {X : List Bool → List Bool} (hX : PolyTimeComputable X)
    {K : List Bool → ℕ} (hK : PolyTimeComputable fun z => List.replicate (K z) true) :
    PolyTimeComputable fun z => List.replicate (countBits (X z) (K z)) true := by
  let upd : List Bool → List Bool := fun w =>
    (pairSndD (pairSndD w) ++
      (if (X (pairFstD w)).getD (pairFstD (pairSndD w)).length false = true then [true] else [])).take
        (K (pairFstD w))
  have hbit : PolyTimeComputable fun w =>
      [(X (pairFstD w)).getD (pairFstD (pairSndD w)).length false] :=
    getBit_poly (hX.comp polyTimeComputable_pairFstD)
      (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  have hupd : PolyTimeComputable upd :=
    truncate_poly ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).append
      (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const [])))
      (unaryComp_poly hK polyTimeComputable_pairFstD)
  obtain ⟨C, c, hC⟩ := hK.output_length_le
  have hKC : ∀ x, K x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hloop := polyTimeComputable_loopState hupd (polyTimeComputable_const []) hK
    (PolyExpr.normal C c) (fun x => by simp) (fun x s => by
      show ((_ : List Bool).take (K (pairFstD (pairEncode x s)))).length ≤ _
      rw [pairFstD_pairEncode]
      exact (List.length_take_le _ _).trans (hKC x))
  convert hloop using 1
  funext z
  have key : ∀ i, i ≤ K z →
      loopState upd (fun _ => []) z i = List.replicate (countBits (X z) i) true := by
    intro i
    induction i with
    | zero => intro _; simp [countBits]
    | succ i ih =>
      intro hi
      rw [loopState_succ, ih (Nat.le_of_succ_le hi)]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      have hle : countBits (X z) i + ((X z).getD i false).toNat ≤ K z := by
        have := countBits_le (X z) (i + 1)
        rw [countBits_succ] at this
        omega
      have hrep : List.replicate (countBits (X z) i) true ++
          (if (X z).getD i false = true then [true] else []) =
          List.replicate (countBits (X z) i + ((X z).getD i false).toNat) true := by
        cases (X z).getD i false
        · simp
        · rw [if_pos rfl, ← List.replicate_succ', Bool.toNat_true]
      rw [hrep, List.take_replicate, min_eq_right hle, countBits_succ]
  exact (key (K z) le_rfl).symm

/-- **Finite table lookup**: for any `f : ℕ → List Bool` and bound `K`, `z ↦ f (min (V z) K)` is
polynomial-time for a unary `V` (induction on `K`, one `polyTimeComputable_ite` per entry). -/
theorem table_poly (f : ℕ → List Bool) {V : List Bool → ℕ}
    (hV : PolyTimeComputable fun z => List.replicate (V z) true) :
    ∀ K : ℕ, PolyTimeComputable fun z => f (min (V z) K)
  | 0 => by simpa using polyTimeComputable_const (f 0)
  | K + 1 => by
    have h := polyTimeComputable_ite (leTest_poly hV (unaryConst_poly K)) (table_poly f hV K)
      (polyTimeComputable_const (f (K + 1)))
    refine ptc_congr h fun z => ?_
    by_cases hz : V z ≤ K
    · simp [hz, min_eq_left (hz.trans (Nat.le_succ K))]
    · simp [hz, min_eq_right (Nat.succ_le_of_lt (not_le.1 hz))]

/-- **The rejection sampler is unary polynomial-time** (`EncodingPermutations.trialIdx_poly`
for the first accepted trial, `blockVal_poly` for its value, `polyTimeComputable_ite`). -/
theorem sampleNum_poly {M K T M' : List Bool → ℕ} {R : List Bool → List Bool}
    (hM : PolyTimeComputable fun z => List.replicate (M z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (T z) true) (hR : PolyTimeComputable R)
    (hM' : PolyTimeComputable fun z => List.replicate (M' z) true) (hKM : ∀ z, 2 ^ K z ≤ M' z) :
    PolyTimeComputable fun z => List.replicate (sampleNum (M z) (K z) (T z) (R z)) true := by
  have htr := trialIdx_poly hM hK hT hR (unaryConst_poly 0) hM' hKM
  have hbv := blockVal_poly hR (unaryMul_poly htr hK) hK hM' hKM
  refine ptc_congr (polyTimeComputable_ite (ltTest_poly htr hT) hbv hM) fun z => ?_
  unfold sampleNum
  by_cases h : trialIdx (M z) (K z) (T z) (R z) 0 < T z <;> simp [h]

/-- Concatenating the first `L` chunks of a longer range. -/
theorem flatMap_range_ite (f : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then f i else []) =
      (List.range (min N L)).flatMap f
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite f L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h), List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, min_eq_right (not_lt.1 h), min_eq_right ((not_lt.1 h).trans (Nat.le_succ N)),
        List.append_nil]

/-- **A loop emitting `L z` chunks is polynomial-time** when the chunk `F z i` is polynomial-time
in `⟨1^i, z⟩`, the count `L` is unary and bounded by `|z| + 1`.

**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` on the counter step
`EncodingMachines.cstep` from `⟨[], z⟩` (orbit `⟨1^i, z⟩`, `cstep_iterate`, bounded by
`cstep_horbit`) with the chunk `F z i` emitted while `i < L z` and nothing afterwards
(`polyTimeComputable_ite`, `ltTest_poly`); the `|z| + 3` emitted chunks concatenate to the
first `L z` ones (`flatMap_range_ite`). -/
theorem emitLoop_poly {F : List Bool → ℕ → List Bool}
    (hF : PolyTimeComputable fun w => F (pairSndD w) (pairFstD w).length)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun z => List.replicate (L z) true)
    (hLle : ∀ z, L z ≤ z.length + 1) :
    PolyTimeComputable fun z => (List.range (L z)).flatMap (F z) := by
  have hemit : PolyTimeComputable fun w =>
      if decide ((pairFstD w).length < L (pairSndD w)) = true then F (pairSndD w) (pairFstD w).length
      else [] :=
    polyTimeComputable_ite (ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
      (unaryComp_poly hL polyTimeComputable_pairSndD)) hF (polyTimeComputable_const [])
  have hE := polyTimeComputable_iterateEmit cstep_poly hemit .var (cbound .var) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  refine ptc_congr (hE.comp hpre) fun z => ?_
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : L z ≤ PolyExpr.var.eval (pairEncode [] z).length + 1 := by
    rw [PolyExpr.eval_var, length_pairEncode]
    have := hLle z
    simp only [List.length_nil]
    omega
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]


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

/-- The second component of a word is no longer than the word. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length :=
  le_trans (Nat.le_add_left _ _) (length_pairFstD_add_pairSndD_le z)

/-- The common input is no longer than the machine input. -/
theorem length_simX_le (w : List Bool) : (simX w).length ≤ w.length :=
  (length_pairFstD_le _).trans ((length_pairSndD_le _).trans
    ((length_pairFstD_le _).trans (length_pairFstD_le _)))

/-! ### The components of one attempt as machines -/

section Components

variable {X Z R : List Bool → List Bool} {T : List Bool → ℕ}

/-- The coin block of attempt `T w` is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly`
at the unary offset `T · B`, `EncodingMachines.truncate_poly` at the unary block length). -/
theorem blk_poly (ℓ : PolyExpr) (V' : Strategy) (hX : PolyTimeComputable X)
    (hT : PolyTimeComputable fun w => List.replicate (T w) true) (hR : PolyTimeComputable R) :
    PolyTimeComputable fun w =>
      colCoinSlice ((blockPoly ℓ V').eval (X w).length) (T w) (R w) := by
  have hB : PolyTimeComputable fun w =>
      List.replicate ((blockPoly ℓ V').eval (X w).length) true :=
    unaryPolyOf_poly (blockPoly ℓ V') (unaryLength_poly hX)
  have hdrop : PolyTimeComputable fun w =>
      (R w).drop (T w * (blockPoly ℓ V').eval (X w).length) := by
    refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryMul_poly hT hB).pairEncode hR)) fun w => ?_
    simp
  exact truncate_poly hdrop hB

/-- The vertex count is unary polynomial-time (`EncodingMachines.unarySqrt_poly`). -/
theorem nV_poly (hX : PolyTimeComputable X) :
    PolyTimeComputable fun w => List.replicate (nV (X w)) true :=
  unarySqrt_poly (unaryLength_poly hX)

/-- The edge count is unary polynomial-time (`countBits_poly`). -/
theorem mE_poly (hX : PolyTimeComputable X) :
    PolyTimeComputable fun w => List.replicate (mE (X w)) true :=
  countBits_poly hX (unaryMul_poly (nV_poly hX) (nV_poly hX))

/-- The offset `baseR` of the commitment randomness is unary polynomial-time. -/
theorem baseR_poly (hX : PolyTimeComputable X) :
    PolyTimeComputable fun w => List.replicate (baseR (X w)) true :=
  unaryAdd_poly (unaryPolyOf_poly (.pow (.add .var (.const 1)) 2) (unaryLength_poly hX))
    (unaryMul_poly (unaryConst_poly 3) (unaryLength_poly hX))

/-- The sampled edge index is unary polynomial-time (`sampleNum_poly` with `Nat.size |E|` bits
and the bound `2^{size |E|} ≤ 2|E| + 1`, `sampleEdgeIdx_eq`). -/
theorem eIdx_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (eIdx (X w) (B w)) true := by
  have hm := mE_poly hX
  have hs := sampleNum_poly hm (unarySize_poly hm) (unaryLength_poly hX) hB
    (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) hm) (unaryConst_poly 1))
    (fun w => two_pow_size_le_two_mul_succ (mE (X w)))
  refine ptc_congr (polyTimeComputable_ite (ltTest_poly hs hm) hs (unaryConst_poly 0)) fun w => ?_
  unfold eIdx
  rw [sampleEdgeIdx_eq]
  by_cases h : sampleNum (mE (X w)) (Nat.size (mE (X w))) (X w).length (B w) < mE (X w) <;>
    simp [h]

/-- The numeric colour-pair sample is unary polynomial-time (`sampleNum_poly` with `3` bits). -/
theorem vIdx_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (vIdx (X w) (B w)) true := by
  have hdrop : PolyTimeComputable fun w => (B w).drop (((X w).length + 1) ^ 2) := by
    refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryPolyOf_poly (.pow (.add .var (.const 1)) 2) (unaryLength_poly hX)).pairEncode hB))
      fun w => ?_
    simp [PolyExpr.eval]
  exact sampleNum_poly (unaryConst_poly 6) (unaryConst_poly 3) (unaryLength_poly hX) hdrop
    (unaryConst_poly 8) (fun _ => by norm_num)

/-- The position of the sampled edge is unary polynomial-time
(`EncodingMachines.polyTimeComputable_firstIdx` with the test "set bit with `e'` set bits
before it", `getBit_poly`, `countBits_poly`, `eqTest_poly`). -/
theorem kPos_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (kPos (X w) (B w)) true := by
  have hp : PolyTimeComputable fun w' =>
      [(X (pairSndD w')).getD (pairFstD w').length false &&
        decide (countBits (X (pairSndD w')) (pairFstD w').length =
          eIdx (X (pairSndD w')) (B (pairSndD w')))] :=
    polyTimeComputable_and
      (getBit_poly (hX.comp polyTimeComputable_pairSndD)
        (unaryLength_poly polyTimeComputable_pairFstD))
      (eqTest_poly (countBits_poly (hX.comp polyTimeComputable_pairSndD)
        (unaryLength_poly polyTimeComputable_pairFstD))
        (unaryComp_poly (eIdx_poly hX hB) polyTimeComputable_pairSndD))
  exact polyTimeComputable_firstIdx
    (p := fun w k => (X w).getD k false && decide (countBits (X w) k = eIdx (X w) (B w))) hp
    (unaryMul_poly (nV_poly hX) (nV_poly hX))

/-- The first endpoint of the sampled edge is unary polynomial-time (`divNum_poly`). -/
theorem p1_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (kPos (X w) (B w) / nV (X w)) true := by
  refine ptc_congr (divNum_poly (kPos_poly hX hB) (nV_poly hX)) fun w => ?_
  rw [divNum_eq]

/-- The second endpoint of the sampled edge is unary polynomial-time (`modNum_poly`). -/
theorem p2_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (kPos (X w) (B w) % nV (X w)) true := by
  refine ptc_congr (modNum_poly (kPos_poly hX hB) (nV_poly hX)) fun w => ?_
  rw [modNum_eq]

/-- The encoding of the first sampled colour is polynomial-time (a six-entry table,
`table_poly`). -/
theorem colA_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => encColor (colorA (vIdx (X w) (B w))) := by
  refine ptc_congr (table_poly (fun j => encColor (colorA j)) (vIdx_poly hX hB) 6) fun w => ?_
  congr 1
  unfold colorA
  by_cases h : vIdx (X w) (B w) < 6
  · rw [min_eq_left h.le]
  · rw [min_eq_right (not_lt.1 h), dif_neg h, dif_neg (lt_irrefl 6)]

/-- The encoding of the second sampled colour is polynomial-time (`table_poly`). -/
theorem colB_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => encColor (colorB (vIdx (X w) (B w))) := by
  refine ptc_congr (table_poly (fun j => encColor (colorB j)) (vIdx_poly hX hB) 6) fun w => ?_
  congr 1
  unfold colorB
  by_cases h : vIdx (X w) (B w) < 6
  · rw [min_eq_left h.le]
  · rw [min_eq_right (not_lt.1 h), dif_neg h, dif_neg (lt_irrefl 6)]

/-- The encoded simulated colour of vertex `I w` is polynomial-time (two comparisons with the
endpoints, `polyTimeComputable_ite`). -/
theorem colorStr_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) {I : List Bool → ℕ}
    (hI : PolyTimeComputable fun w => List.replicate (I w) true) :
    PolyTimeComputable fun w => encColor (colorNum (X w) (B w) (I w)) := by
  have h := polyTimeComputable_ite (eqTest_poly hI (p1_poly hX hB)) (colA_poly hX hB)
    (polyTimeComputable_ite (eqTest_poly hI (p2_poly hX hB)) (colB_poly hX hB)
      (polyTimeComputable_const (encColor 0)))
  refine ptc_congr h fun w => ?_
  unfold colorNum
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- The commitment randomness of vertex `I w` is polynomial-time
(`EnsembleLemmas.polyTimeComputable_padL` after the unary offset). -/
theorem rrStr_poly (ℓ : PolyExpr) (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) {I : List Bool → ℕ}
    (hI : PolyTimeComputable fun w => List.replicate (I w) true) :
    PolyTimeComputable fun w => rrStr ℓ (X w) (B w) (I w) := by
  have hℓn : PolyTimeComputable fun w => List.replicate (ℓ.eval (nV (X w))) true :=
    unaryPolyOf_poly ℓ (nV_poly hX)
  have hdrop : PolyTimeComputable fun w =>
      (B w).drop (baseR (X w) + I w * ℓ.eval (nV (X w))) := by
    refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryAdd_poly (baseR_poly hX) (unaryMul_poly hI hℓn)).pairEncode hB)) fun w => ?_
    simp
  refine ptc_congr (EnsembleLemmas.polyTimeComputable_padL ℓ (nV_poly hX) hdrop) fun w => ?_
  simp [rrStr]

/-- One encoded commitment of the vector is polynomial-time (`hCom` on the padded colour and
the randomness). -/
theorem chunk_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    (hX : PolyTimeComputable X) {B : List Bool → List Bool} (hB : PolyTimeComputable B)
    {c : List Bool → ℕ → Fin 3} {I : List Bool → ℕ}
    (hI : PolyTimeComputable fun w => List.replicate (I w) true)
    (hc : PolyTimeComputable fun w => encColor (c w (I w))) :
    PolyTimeComputable fun w => chunk Com ℓ (X w) (B w) (c w) (I w) := by
  have hpad : PolyTimeComputable fun w => EnsembleLemmas.padL (nV (X w)) (encColor (c w (I w))) := by
    refine ptc_congr (EnsembleLemmas.polyTimeComputable_padL .var (nV_poly hX) hc) fun w => ?_
    simp
  exact (hCom.comp (hpad.pairEncode (rrStr_poly ℓ hX hB hI))).pairEncode
    (polyTimeComputable_const [])

/-- The simulated commitment message is polynomial-time (`emitLoop_poly` over the vertices). -/
theorem comStr_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    (hX : PolyTimeComputable X) (hXle : ∀ w, (X w).length ≤ w.length)
    {B : List Bool → List Bool} (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => comStr Com ℓ (X w) (B w) (colorNum (X w) (B w)) := by
  have hF := chunk_poly hCom ℓ (hX.comp polyTimeComputable_pairSndD)
    (hB.comp polyTimeComputable_pairSndD)
    (c := fun w' => colorNum (X (pairSndD w')) (B (pairSndD w')))
    (unaryLength_poly polyTimeComputable_pairFstD)
    (colorStr_poly (hX.comp polyTimeComputable_pairSndD) (hB.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))
  exact emitLoop_poly (F := fun w i => chunk Com ℓ (X w) (B w) (colorNum (X w) (B w)) i) hF
    (nV_poly hX) (fun w => (Nat.sqrt_le_self _).trans ((hXle w).trans (Nat.le_succ _)))

/-- The all-zero commitment message is polynomial-time (`emitLoop_poly`). -/
theorem comStr0_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    (hX : PolyTimeComputable X) (hXle : ∀ w, (X w).length ≤ w.length)
    {B : List Bool → List Bool} (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => comStr Com ℓ (X w) (B w) (fun _ => 0) := by
  have hF := chunk_poly hCom ℓ (hX.comp polyTimeComputable_pairSndD)
    (hB.comp polyTimeComputable_pairSndD) (c := fun _ _ => 0)
    (unaryLength_poly polyTimeComputable_pairFstD) (polyTimeComputable_const (encColor 0))
  exact emitLoop_poly (F := fun w i => chunk Com ℓ (X w) (B w) (fun _ => 0) i) hF
    (nV_poly hX) (fun w => (Nat.sqrt_le_self _).trans ((hXle w).trans (Nat.le_succ _)))

/-- The tape handed to `V'` is polynomial-time. -/
theorem rVStr_poly (ℓ : PolyExpr) (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => rVStr ℓ (X w) (B w) := by
  have hN := unaryLength_poly hX
  have hlen : PolyTimeComputable fun w =>
      List.replicate (baseR (X w) + (X w).length * ℓ.eval (X w).length) true :=
    unaryAdd_poly (baseR_poly hX) (unaryMul_poly hN (unaryPolyOf_poly ℓ hN))
  refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp (hlen.pairEncode hB)) fun w => ?_
  simp [rVStr]

/-- The reply of an efficient `V'` to the commitment message is polynomial-time: one activation
of its machine on the layout `⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, ⟨com, []⟩⟩⟩, []⟩, r_V⟩`
(`Strategy.ofNUPPT_next`, `NUPPT.runAtL_eq_output_layout`, `NUPPT.polyTimeComputable_layout`). -/
theorem reply_poly (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) (hX : PolyTimeComputable X)
    (hZ : PolyTimeComputable Z) {B : List Bool → List Bool} (hB : PolyTimeComputable B)
    {C : List Bool → List Bool} (hC : PolyTimeComputable C) :
    PolyTimeComputable fun w => V'.next (X w) (Z w) (rVStr ℓ (X w) (B w)) [C w] := by
  obtain ⟨A, hA, -, hnext⟩ := hV'
  have hlay := NUPPT.polyTimeComputable_layout (polyTimeComputable_unary.comp hX)
    ((hX.pairEncode hZ).pairEncode (hC.pairEncode (polyTimeComputable_const [])))
    (polyTimeComputable_const []) (rVStr_poly ℓ hX hB)
  refine ptc_congr (A.polyTimeComputable_output.comp hlay) fun w => ?_
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq]
  rfl

/-- The opening message is polynomial-time. -/
theorem opnStr_poly (ℓ : PolyExpr) (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => opnStr ℓ (X w) (B w) :=
  ((colorStr_poly hX hB (p1_poly hX hB)).pairEncode (rrStr_poly ℓ hX hB (p1_poly hX hB))).pairEncode
    ((colorStr_poly hX hB (p2_poly hX hB)).pairEncode (rrStr_poly ℓ hX hB (p2_poly hX hB)))

/-- An encoded two-message view is polynomial-time in its components. -/
theorem view_poly (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    {Rv C O : List Bool → List Bool} (hRv : PolyTimeComputable Rv) (hC : PolyTimeComputable C)
    (hO : PolyTimeComputable O) :
    PolyTimeComputable fun w => View.encode ⟨X w, Z w, Rv w, [C w, O w]⟩ :=
  (hX.pairEncode hZ).pairEncode
    (hRv.pairEncode (hC.pairEncode (hO.pairEncode (polyTimeComputable_const []))))

/-- **One attempt is polynomial-time**: both the success test and the (defaulted) view of
`attemptNum` on polynomial-time inputs `X, Z, B`.

**Proof sketch.** Assemble the components: the edge count (`mE_poly`), the commitment messages
(`comStr_poly`, `comStr0_poly`), the tape (`rVStr_poly`), `V'`'s reply (`reply_poly`), the
test `|reply| % |E| = e'` (`modNum_poly`, `eqTest_poly`), the opening (`opnStr_poly`) and the
views (`view_poly`); the success test is `|E| = 0 ∨ test` and the output a two-way
`polyTimeComputable_ite`. -/
theorem attemptNum_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) (hX : PolyTimeComputable X)
    (hXle : ∀ w, (X w).length ≤ w.length) (hZ : PolyTimeComputable Z)
    {B : List Bool → List Bool} (hB : PolyTimeComputable B) :
    PolyTimeComputable (fun w => [(attemptNum Com ℓ V' (X w) (Z w) (B w)).isSome]) ∧
    PolyTimeComputable (fun w => (attemptNum Com ℓ V' (X w) (Z w) (B w)).getD []) := by
  have hm := mE_poly hX
  have hcom := comStr_poly hCom ℓ hX hXle hB
  have hcom0 := comStr0_poly hCom ℓ hX hXle hB
  have hrV := rVStr_poly ℓ hX hB
  have hreply := reply_poly ℓ hV' hX hZ hB hcom
  have htest : PolyTimeComputable fun w =>
      [decide ((V'.next (X w) (Z w) (rVStr ℓ (X w) (B w))
        [comStr Com ℓ (X w) (B w) (colorNum (X w) (B w))]).length % mE (X w) =
          eIdx (X w) (B w))] := by
    refine ptc_congr (eqTest_poly (modNum_poly (unaryLength_poly hreply) hm) (eIdx_poly hX hB))
      fun w => ?_
    rw [modNum_eq]
  have hzero : PolyTimeComputable fun w => [decide (mE (X w) = 0)] :=
    eqTest_poly hm (unaryConst_poly 0)
  have hview := view_poly hX hZ hrV hcom (opnStr_poly ℓ hX hB)
  have hview0 := view_poly hX hZ hrV hcom0 (polyTimeComputable_const [])
  refine ⟨?_, ?_⟩
  · refine ptc_congr (or_poly hzero htest) fun w => ?_
    unfold attemptNum
    by_cases h0 : mE (X w) = 0
    · simp [h0]
    · by_cases ht : (V'.next (X w) (Z w) (rVStr ℓ (X w) (B w))
          [comStr Com ℓ (X w) (B w) (colorNum (X w) (B w))]).length % mE (X w) =
            eIdx (X w) (B w) <;> simp [h0, ht]
  · refine ptc_congr (polyTimeComputable_ite hzero hview0
      (polyTimeComputable_ite htest hview (polyTimeComputable_const []))) fun w => ?_
    unfold attemptNum
    by_cases h0 : mE (X w) = 0
    · simp [h0]
    · by_cases ht : (V'.next (X w) (Z w) (rVStr ℓ (X w) (B w))
          [comStr Com ℓ (X w) (B w) (colorNum (X w) (B w))]).length % mE (X w) =
            eIdx (X w) (B w) <;> simp [h0, ht]

end Components

/-! ### The attempts on the layout and the loop over them -/

/-- The attempt of the simulator at index `t` on the layout `w`, in numeric form. -/
noncomputable def attemptAt (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (w : List Bool) (t : ℕ) : Option (List Bool) :=
  attemptNum Com ℓ V' (simX w) (simZ w)
    (colCoinSlice ((blockPoly ℓ V').eval (simX w).length) t (simR w))

/-- **One attempt on the indexed layout `⟨1^t, w⟩` is polynomial-time** (`attemptNum_poly` on
the projections of the layout, the block cut by `blk_poly`). -/
theorem attemptAt_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) :
    PolyTimeComputable (fun u => [(attemptAt Com ℓ V' (pairSndD u) (pairFstD u).length).isSome]) ∧
    PolyTimeComputable (fun u => (attemptAt Com ℓ V' (pairSndD u) (pairFstD u).length).getD []) :=
  attemptNum_poly hCom ℓ hV' (X := fun u => simX (pairSndD u))
    (simX_poly.comp polyTimeComputable_pairSndD)
    (fun u => (length_simX_le _).trans (length_pairSndD_le u))
    (Z := fun u => simZ (pairSndD u)) (simZ_poly.comp polyTimeComputable_pairSndD)
    (B := fun u => colCoinSlice ((blockPoly ℓ V').eval (simX (pairSndD u)).length)
      (pairFstD u).length (simR (pairSndD u)))
    (blk_poly ℓ V' (simX_poly.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD) (simR_poly.comp polyTimeComputable_pairSndD))

/-- The simulator on its layout, through the first accepted attempt.

**Proof sketch.** Every attempt is its numeric form (`attemptStr_eq_attemptNum`), the edge
count is `mE` (`edgeCount_eq_countBits`) and the iteration count `n|E|` is `nV · mE`; the
search `List.findSome?` over the attempts is the attempt at the first accepted index
(`findSome?_range_eq`). -/
theorem sim_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy) (w : List Bool) :
    sim Com ℓ V' (simX w) (simZ w) (simR w) =
      if mE (simX w) = 0 then (attemptAt Com ℓ V' w 0).getD []
      else if firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome) (nV (simX w) * mE (simX w)) <
          nV (simX w) * mE (simX w) then
        (attemptAt Com ℓ V' w
          (firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome) (nV (simX w) * mE (simX w)))).getD []
      else [] := by
  have hm : edgeCount (decGraph (simX w)).2 = mE (simX w) := edgeCount_eq_countBits _
  have hit : colIterations (simX w) = nV (simX w) * mE (simX w) := by
    unfold colIterations
    rw [hm]
    rfl
  have hatt : (fun t => attemptStr Com ℓ V' (simX w) (simZ w)
      (colCoinSlice ((blockPoly ℓ V').eval (simX w).length) t (simR w))) = attemptAt Com ℓ V' w := by
    funext t
    exact attemptStr_eq_attemptNum Com ℓ V' _ _ _
  have hatt0 : attemptStr Com ℓ V' (simX w) (simZ w)
      (colCoinSlice ((blockPoly ℓ V').eval (simX w).length) 0 (simR w)) = attemptAt Com ℓ V' w 0 :=
    attemptStr_eq_attemptNum Com ℓ V' _ _ _
  unfold sim
  simp only [hm, hit, hatt, hatt0]
  rw [findSome?_range_eq]
  by_cases h0 : mE (simX w) = 0
  · simp [h0]
  · by_cases hlt : firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome)
        (nV (simX w) * mE (simX w)) < nV (simX w) * mE (simX w) <;> simp [h0, hlt]

/-- **The simulator is polynomial-time** as a function of its machine layout.

**Proof sketch.** The first accepted attempt index is
`EncodingMachines.polyTimeComputable_firstIdx` with the success test of `attemptAt_poly` and
the unary bound `nV · mE`; the output is that attempt's view (`attemptAt_poly` on
`⟨1^{index}, w⟩`) or `[]`, and the single attempt `0` when `E = ∅`; `sim_eq` identifies the
cases. -/
theorem sim_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    {V' : Strategy} (hV' : V'.Efficient) :
    PolyTimeComputable fun w => sim Com ℓ V' (simX w) (simZ w) (simR w) := by
  obtain ⟨hp, hout⟩ := attemptAt_poly hCom ℓ hV'
  have hm : PolyTimeComputable fun w => List.replicate (mE (simX w)) true := mE_poly simX_poly
  have hlen : PolyTimeComputable fun w => List.replicate (nV (simX w) * mE (simX w)) true :=
    unaryMul_poly (nV_poly simX_poly) hm
  have hidx := polyTimeComputable_firstIdx (p := fun w t => (attemptAt Com ℓ V' w t).isSome) hp hlen
  have hsel : PolyTimeComputable fun w => (attemptAt Com ℓ V' w
      (firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome) (nV (simX w) * mE (simX w)))).getD [] := by
    refine ptc_congr (hout.comp (hidx.pairEncode polyTimeComputable_id)) fun w => ?_
    simp
  have h0 : PolyTimeComputable fun w => (attemptAt Com ℓ V' w 0).getD [] := by
    refine ptc_congr (hout.comp ((polyTimeComputable_const []).pairEncode polyTimeComputable_id))
      fun w => ?_
    simp
  refine ptc_congr (polyTimeComputable_ite (eqTest_poly hm (unaryConst_poly 0)) h0
    (polyTimeComputable_ite (ltTest_poly hidx hlen) hsel (polyTimeComputable_const []))) fun w => ?_
  rw [sim_eq]
  by_cases hz : mE (simX w) = 0
  · simp [hz]
  · by_cases hlt : firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome)
        (nV (simX w) * mE (simX w)) < nV (simX w) * mE (simX w) <;> simp [hz, hlt]

/-- **The simulator is a uniform PPT** (Claim-128.a, shadow form): `NUPPT.ofPolyTimeUniform`
of `sim_poly` with the coin polynomial `simCoins ℓ V'` computes `sim Com ℓ V' x z r` on
`⟨x, z⟩` at parameter `|x|` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_simulator {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = simCoins ℓ V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = sim Com ℓ V' x z (List.ofFn r) := by
  have hF := sim_poly hCom ℓ hV'
  refine ⟨NUPPT.ofPolyTimeUniform hF (simCoins ℓ V'), NUPPT.ofPolyTimeUniform_uniform _ _, rfl, ?_⟩
  intro x z r
  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [simX, simZ, simR, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

end TCSlib.Cryptography.ColSimMachine
