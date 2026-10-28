/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: machines behind the honest parties

Proof infrastructure for the efficiency theorems of `ThreeColoring/Protocol.lean`
(`colProver_efficient`, `colVerifier_efficient`, `colProverRep_efficient`,
`colVerifierRep_efficient`, inventory item Inf-4.2) and for the decider clause of
`R3COL_witnessRelation` [PS10, §4.7, Protocol 127.5]. The honest parties of the protocol
are exhibited as polynomial-time functions of the interactive machine layout
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`ilayout`, `efficient_of_polyTime`), assembled from
the unary FP toolkit of `ZeroKnowledge/EncodingMachines.lean` (numbers travel in unary,
`polyTimeComputable_firstIdx`, `polyTimeComputable_of_getD`, `polyTimeComputable_stateFind`)
and the typed coin cuts of `Complexity/Randomized/Primitives.lean`.

This file holds the generic pieces (the parties themselves as string functions are in
`ThreeColoring/Parties.lean`, the identification with the strategies of `Protocol.lean` in
`ThreeColoring/ProtocolProofs.lean`):

* counted loops bounded along the genuine orbit only (`polyTimeComputable_loopState'`),
  concatenating loops over a data-dependent range (`polyTimeComputable_flatMap_range`), and
  the iterated second projection (`iterSnd_poly`, the message-selection `msgAt`);
* zero padding (`padTo`) with the identities `List.ofFn (padFin L w) = padTo L w` and
  `List.ofFn (fun j => r.getD (b + j) false) = padTo L (r.drop b)` that turn the parties'
  typed values and randomness blocks into string operations;
* the **numeric model of the edge list**: `edgeList G` is, through the index
  `(u, v) ↦ v + n u` of `finProdFinEquiv`, the increasing list of positions `j < n²` whose
  bit of the adjacency matrix is set (`map_edgeList`); hence `edgeCount G` is the bit count
  `countTrue` and `edgeOf G e` is the `e`-th set position `nthTrue` (`edgeCount_eq`,
  `edgeOf_val`), both computed by counted loops and bounded searches;
* the **numeric model of the samplers**: `bitsToNat` of a tape window is the loop value
  `natOfBits`, and the rejection sampler is the first accepted trial (`sampleVal`,
  `map_val_sampleIdx_getD`); the colour permutation reaches the machine as the six-bit table
  `permTable π` of the images of the three colours (`permTable_samplePerm3`), a table lookup
  on the sampled index;
* colours as numbers: `decColoring`, `decColor` and `encColor` numerically (`colorVal`,
  `encColorOfVal`, `colorFromTable`).

## Main results

* `TCSlib.Cryptography.ColMachines.polyTimeComputable_loopState'`,
  `ColMachines.polyTimeComputable_flatMap_range`, `ColMachines.iterSnd_poly` — loops.
* `TCSlib.Cryptography.ColMachines.map_edgeList`, `ColMachines.edgeCount_eq`,
  `ColMachines.edgeOf_val` — the numeric model of the edge list.
* `TCSlib.Cryptography.ColMachines.map_val_sampleIdx_getD`, `ColMachines.permTable_samplePerm3`
  — the numeric model of the samplers.
* `TCSlib.Cryptography.ColMachines.countTrue_poly`, `ColMachines.nthTrue_poly`,
  `ColMachines.natOfBits_poly`, `ColMachines.sampleVal_poly`, `ColMachines.tableOfIdx_poly`,
  `ColMachines.colorVal_poly`, `ColMachines.encColorOfVal_poly` — the unary machines.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### Generic tools -/

/-- Polynomial-time computability transfers along pointwise equality. -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- Composition of polynomial-time functions in applied form (`fun z => g (f z)` rather than
`g ∘ f`, so that later unifications never have to unfold `Function.comp` against a large
definition). -/
theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- **Counted loops bounded along the genuine orbit:** `EncodingMachines.polyTimeComputable_loopState`
with the length bound required only of the states `loopState upd init x i`, `i ≤ N x`
(the update may lengthen arbitrary words). Same proof: a state loop
(`EncodingMachines.polyTimeComputable_stateFind`, data in `EncodingMachines.CountLoop`). -/
theorem polyTimeComputable_loopState' {upd init : List Bool → List Bool}
    (hupd : PolyTimeComputable upd) (hinit : PolyTimeComputable init)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true)
    (B : PolyExpr)
    (hstate : ∀ x i, i ≤ N x → (loopState upd init x i).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => loopState upd init x (N x) := by
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNR : ∀ x, N x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hbound : ∀ x i, i ≤ N x →
      (orbit (CountLoop.start init) (CountLoop.step upd) x i).length ≤
        (PolyExpr.add (.mul (.const 2) (PolyExpr.normal C c)) (.add (.const 2) B)).eval
          x.length := by
    intro x i hi
    rw [CountLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have h1 := hstate x i hi
    have h2 := hNR x
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hfirst : ∀ x i, i < N x →
      CountLoop.acc N (pairEncode x (orbit (CountLoop.start init) (CountLoop.step upd) x i)) =
        false := by
    intro x i hi
    rw [CountLoop.orbit_eq]
    simp [CountLoop.acc, hi]
  have hlast : ∀ x, CountLoop.acc N
      (pairEncode x (orbit (CountLoop.start init) (CountLoop.step upd) x (N x))) = true := by
    intro x
    rw [CountLoop.orbit_eq]
    simp [CountLoop.acc]
  have h := polyTimeComputable_stateFind (CountLoop.start_poly hinit) (CountLoop.step_poly hupd)
    (CountLoop.acc_poly hN) CountLoop.out_poly (PolyExpr.normal C c) _ N hNR hbound hfirst hlast
  convert h using 1
  funext x
  rw [CountLoop.orbit_eq]
  simp [CountLoop.out]

/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
`E i` over `i < min N L` (`EncodingMachines.flatMap_range_ite_eq` for arbitrary chunks). -/
theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
      (List.range (min N L)).flatMap E
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite E L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- **Concatenating loops over a data-dependent range:** if the chunk `E z i` is a
polynomial-time function of `⟨1^i, z⟩` and the range `n z` is a unary function, then
`z ↦ E z 0 ++ ⋯ ++ E z (n z - 1)` is polynomial-time computable (an instance of
`Complexity.polyTimeComputable_iterateEmit` on the counter step `EncodingMachines.cstep`, as
`EncodingMachines.polyTimeComputable_of_getD`). -/
theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
  obtain ⟨C, c, hC⟩ := hn.output_length_le
  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD) (hn.comp polyTimeComputable_pairSndD)
  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hL.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]

/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
polynomial-time `s` and a unary `i`: a counted loop whose states never exceed `|s z|`
(`Complexity.StateLoop.length_pairFstD_add_pairSndD_le`). -/
theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
  have hupd : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hclosed : ∀ z j, loopState (fun w => pairSndD (pairSndD (pairSndD w))) s z j =
      pairSndD^[j] (s z) := by
    intro z j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [loopState_succ, ih, pairSndD_pairEncode, pairSndD_pairEncode,
        Function.iterate_succ_apply']
  have hlen : ∀ (w : List Bool) (j : ℕ), (pairSndD^[j] w).length ≤ w.length := by
    intro w j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ((Nat.le_add_left _ _).trans (length_pairFstD_add_pairSndD_le _)).trans ih
  obtain ⟨C, c, hC⟩ := hs.output_length_le
  have h := polyTimeComputable_loopState' hupd hs hi (PolyExpr.normal C c) fun z j _ => by
    rw [hclosed]
    exact (hlen _ _).trans (by simpa [PolyExpr.eval_normal] using hC z)
  convert h using 1
  funext z
  rw [hclosed]

/-! ### The interactive layout and its projections -/

/-- The interactive machine layout of a strategy activation,
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`Strategy.ofNUPPT`, `NUPPT.runAtL`). -/
def ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) : List Bool :=
  NUPPT.layout (List.replicate x.length true)
    (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r

/-- A strategy whose next-message function is a polynomial-time function `F` of the machine
layout `ilayout x z hist r` is efficient: `NUPPT.ofPolyTimeUniform` of `F` with the strategy's
coin polynomial is the uniform machine computing it (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem efficient_of_polyTime (S : Strategy) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (h : ∀ x z r hist, S.next x z r hist = F (ilayout x z hist r)) : S.Efficient :=
  ⟨NUPPT.ofPolyTimeUniform hF S.coins, NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => by
      rw [h, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-- The common-input slot of the interactive layout. -/
def argX (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inArg w))

/-- The auxiliary-input slot of the interactive layout. -/
def argZ (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg w))

/-- The encoded-messages slot of the interactive layout. -/
def argM (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

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

/-- The common-input projection is polynomial-time. -/
theorem argX_poly : PolyTimeComputable argX :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The auxiliary-input projection is polynomial-time. -/
theorem argZ_poly : PolyTimeComputable argZ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The messages projection is polynomial-time. -/
theorem argM_poly : PolyTimeComputable argM :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-! ### Zero padding -/

/-- `L` zeros from a unary length (the bit-extraction principle with the constant bit `0`). -/
theorem zeros_poly {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => List.replicate (L x) false := by
  refine polyTimeComputable_of_getD (F := fun x => List.replicate (L x) false) ?_ ?_
  · convert polyTimeComputable_const [false] using 1
    funext w
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  · simpa using hL

/-- Padding a word with zeros to length `L` (and truncating to `L`): the string form of the
typed value `padFin L w` (`ofFn_padFin`). -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- Padding to a unary length is polynomial-time. -/
theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => padTo (L x) (s x) :=
  truncate_poly (hs.append (zeros_poly hL)) hL

/-- The padded word has length `L`. -/
theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
  simp [padTo]

/-- The bits of the padded word below `L` are the bits of `w` read with default `false`. -/
theorem getD_padTo (L : ℕ) (w : List Bool) {i : ℕ} (hi : i < L) :
    (padTo L w).getD i false = w.getD i false := by
  rw [padTo, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_append,
    List.getD_eq_getElem?_getD]
  split_ifs with h
  · rfl
  · have hw : w[i]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [hw, List.getElem?_replicate]
    split_ifs <;> rfl

/-- The typed value `padFin L w` as a string is the padded word. -/
theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
  apply List.ext_getElem
  · simp [length_padTo]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    show w.getD i false = (padTo L w)[i]
    rw [← getD_padTo L w (by simpa [length_padTo] using h2), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

/-- A block of `L` bits read with default `false` from position `b` of a tape is the padded
`drop`. -/
theorem ofFn_getD_add (r : List Bool) (b L : ℕ) :
    List.ofFn (fun j : Fin L => r.getD (b + j) false) = padTo L (r.drop b) := by
  rw [← ofFn_padFin]
  congr 1
  funext j
  simp [padFin, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ### Counting set bits -/

/-- The number of set bits among the first `j` positions of `x` (read with default `false`). -/
def countTrue (x : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => countTrue x j + (x.getD j false).toNat

@[simp] theorem countTrue_zero (x : List Bool) : countTrue x 0 = 0 := rfl

@[simp] theorem countTrue_succ (x : List Bool) (j : ℕ) :
    countTrue x (j + 1) = countTrue x j + (x.getD j false).toNat := rfl

/-- At most `j` of the first `j` bits are set. -/
theorem countTrue_le (x : List Bool) (j : ℕ) : countTrue x j ≤ j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [countTrue_succ]
    have := Bool.toNat_le (x.getD j false)
    omega

/-- The bit count is monotone in the prefix length. -/
theorem countTrue_mono (x : List Bool) {i j : ℕ} (h : i ≤ j) : countTrue x i ≤ countTrue x j := by
  induction j with
  | zero =>
    rw [Nat.le_zero.1 h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [countTrue_succ]
      exact (ih (by omega)).trans (Nat.le_add_right _ _)
    · rw [show i = j + 1 by omega]

/-- The unary bit count of a prefix of a polynomial-time word is polynomial-time: a counted
loop appending a token for each set bit (`polyTimeComputable_loopState'`, states of length
`countTrue ≤ N`). -/
theorem countTrue_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun z => List.replicate (N z) true) :
    PolyTimeComputable fun z => List.replicate (countTrue (s z) (N z)) true := by
  let upd : List Bool → List Bool := fun w =>
    if (s (pairFstD w)).getD (pairFstD (pairSndD w)).length false then
      true :: pairSndD (pairSndD w) else pairSndD (pairSndD w)
  have hupd : PolyTimeComputable upd :=
    polyTimeComputable_ite
      (getBit_poly (hs.comp polyTimeComputable_pairFstD)
        (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hclosed : ∀ z i, loopState upd (fun _ => []) z i =
      List.replicate (countTrue (s z) i) true := by
    intro z i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [loopState_succ, ih]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        countTrue_succ]
      cases (s z).getD i false <;> simp [List.replicate_succ]
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have h := polyTimeComputable_loopState' hupd (polyTimeComputable_const []) hN
    (PolyExpr.normal C c) fun z i hi => by
      rw [hclosed, List.length_replicate]
      exact (countTrue_le _ _).trans (hi.trans (by simpa [PolyExpr.eval_normal] using hC z))
  convert h using 1
  funext z
  rw [hclosed]

/-! ### The `e`-th set bit -/

/-- The position of the `e`-th set bit (0-based) among the first `N` positions of `x`: the
least `j < N` whose bit is set and preceded by exactly `e` set bits, `N` if there is none. -/
noncomputable def nthTrue (x : List Bool) (N e : ℕ) : ℕ :=
  firstIdx (fun j => x.getD j false && decide (countTrue x j = e)) N

/-- The `e`-th set position in unary is polynomial-time (`polyTimeComputable_firstIdx` with
the test `bit j ∧ countTrue j = e` on `⟨1^j, z⟩`). -/
theorem nthTrue_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun z => List.replicate (N z) true)
    {e : List Bool → ℕ} (he : PolyTimeComputable fun z => List.replicate (e z) true) :
    PolyTimeComputable fun z => List.replicate (nthTrue (s z) (N z) (e z)) true :=
  polyTimeComputable_firstIdx
    (p := fun z j => (s z).getD j false && decide (countTrue (s z) j = e z))
    (polyTimeComputable_and
      (getBit_poly (hs.comp polyTimeComputable_pairSndD) (unaryLength_poly polyTimeComputable_pairFstD))
      (eqTest_poly
        (countTrue_poly (hs.comp polyTimeComputable_pairSndD)
          (unaryLength_poly polyTimeComputable_pairFstD))
        (he.comp polyTimeComputable_pairSndD)))
    hN

/-- Filtering `List.range (N + 1)` by the bits of `x` appends position `N` iff its bit is set. -/
theorem filter_range_succ (x : List Bool) (N : ℕ) :
    (List.range (N + 1)).filter (fun j => x.getD j false) =
      (List.range N).filter (fun j => x.getD j false) ++ (if x.getD N false then [N] else []) := by
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]

/-- The filtered range has `countTrue x N` elements. -/
theorem length_filter_range (x : List Bool) (N : ℕ) :
    ((List.range N).filter (fun j => x.getD j false)).length = countTrue x N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [filter_range_succ, List.length_append, ih, countTrue_succ]
    cases x.getD N false <;> simp

/-- The `e`-th element of the filtered range is the set position `j` preceded by exactly `e`
set bits. -/
theorem getElem?_filter_range (x : List Bool) {N e j : ℕ} (hj : j < N)
    (hbit : x.getD j false = true) (hcnt : countTrue x j = e) :
    ((List.range N).filter (fun j => x.getD j false))[e]? = some j := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [filter_range_succ]
    rcases Nat.lt_or_ge j N with h | h
    · have hlt : e < countTrue x N := by
        have h1 := countTrue_mono x (Nat.succ_le_of_lt h)
        rw [countTrue_succ, hbit, hcnt] at h1
        simpa using h1
      rw [List.getElem?_append_left (by rw [length_filter_range]; exact hlt)]
      exact ih h
    · have hjN : j = N := by omega
      subst hjN
      rw [List.getElem?_append_right (by rw [length_filter_range, hcnt]),
        length_filter_range, hcnt, Nat.sub_self, if_pos hbit]
      rfl

/-- Every rank `e < countTrue x N` is realised by a set position below `N`. -/
theorem exists_nth_set (x : List Bool) :
    ∀ N e, e < countTrue x N → ∃ j < N, x.getD j false = true ∧ countTrue x j = e := by
  intro N
  induction N with
  | zero => intro e h; simp at h
  | succ N ih =>
    intro e he
    rcases Nat.lt_or_ge e (countTrue x N) with h | h
    · obtain ⟨j, hj, hb, hc⟩ := ih e h
      exact ⟨j, by omega, hb, hc⟩
    · rw [countTrue_succ] at he
      have hb : x.getD N false = true := by
        cases hx : x.getD N false
        · rw [hx] at he; simp at he; omega
        · rfl
      refine ⟨N, Nat.lt_succ_self N, hb, ?_⟩
      rw [hb] at he
      simp at he
      omega

/-- For `e < countTrue x N`, `nthTrue x N e` is below `N`, its bit is set, and exactly `e` set
bits precede it. -/
theorem nthTrue_spec (x : List Bool) {N e : ℕ} (he : e < countTrue x N) :
    nthTrue x N e < N ∧ x.getD (nthTrue x N e) false = true ∧ countTrue x (nthTrue x N e) = e := by
  obtain ⟨j, hj, hb, hc⟩ := exists_nth_set x N e he
  have hlt : nthTrue x N e < N := by
    refine firstIdx_lt_iff.2 ⟨j, hj, ?_⟩
    rw [hb, hc]
    simp
  have hq := q_firstIdx (q := fun j => x.getD j false && decide (countTrue x j = e)) hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨hlt, hq.1, hq.2⟩

/-- The `e`-th element of the filtered range is `nthTrue x N e`. -/
theorem getElem?_filter_range_nthTrue (x : List Bool) {N e : ℕ} (he : e < countTrue x N) :
    ((List.range N).filter (fun j => x.getD j false))[e]? = some (nthTrue x N e) :=
  let h := nthTrue_spec x he
  getElem?_filter_range x h.1 h.2.1 h.2.2

/-! ### The numeric model of the edge list -/

/-- The row-major indices of the lexicographically ordered pairs `Fin m × Fin n` enumerate
`range (m n)`. -/
theorem flatMap_range_mul (n : ℕ) :
    ∀ m, (List.range m).flatMap (fun u => (List.range n).map (fun v => v + n * u)) =
      List.range (m * n)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_mul n m, List.flatMap_singleton,
      Nat.succ_mul, List.range_add]
    congr 1
    apply List.map_congr_left
    intro v _
    ring

/-- The indices `v + n u` of the lexicographically ordered pairs of `finRange n ×ˢ finRange n`
enumerate `range (n²)` (`finProdFinEquiv`). -/
theorem map_product_finRange (n : ℕ) :
    (List.finRange n ×ˢ List.finRange n).map
        (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)) =
      List.range (n * n) := by
  rw [← flatMap_range_mul n n]
  show (List.product (List.finRange n) (List.finRange n)).map _ = _
  unfold List.product
  rw [List.map_flatMap]
  conv_rhs => rw [← List.map_coe_finRange n, List.flatMap_map]
  congr 1
  funext u
  rw [List.map_map, List.map_map]
  congr 1

/-- **The numeric model of the edge list:** through the index `(u, v) ↦ v + n u` of
`finProdFinEquiv`, the lexicographically ordered edge list of a graph whose adjacency bit
`(u, v)` is bit `v + n u` of the word `x` is the increasing list of set positions `j < n²` of
`x` (`List.filter_map` and `map_product_finRange`). -/
theorem map_edgeList {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) :
    (edgeList G).map (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)) =
      (List.range (n * n)).filter (fun j => x.getD j false) := by
  rw [← map_product_finRange, List.filter_map]
  unfold edgeList
  congr 1
  apply List.filter_congr
  rintro ⟨u, v⟩ _
  exact hG u v

/-- The number of edges is the number of set bits among the `n²` matrix positions. -/
theorem edgeCount_eq {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) :
    edgeCount G = countTrue x (n * n) := by
  have := congrArg List.length (map_edgeList G x hG)
  rwa [List.length_map, length_filter_range] at this

/-- The endpoints of the edge of index `e` are the quotient and remainder by `n` of the
`e`-th set position `nthTrue x (n²) e` of the adjacency word. -/
theorem edgeOf_val {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) (e : Fin (edgeCount G)) :
    ((edgeOf G e).1 : ℕ) = nthTrue x (n * n) e / n ∧
      ((edgeOf G e).2 : ℕ) = nthTrue x (n * n) e % n := by
  have he : (e : ℕ) < countTrue x (n * n) := by
    rw [← edgeCount_eq G x hG]
    exact e.isLt
  have h1 : ((edgeList G).map
      (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)))[(e : ℕ)]? =
      some ((finProdFinEquiv (edgeOf G e) : Fin (n * n)) : ℕ) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem e.isLt, Option.map_some]
    rfl
  rw [map_edgeList G x hG, getElem?_filter_range_nthTrue x he, Option.some.injEq,
    finProdFinEquiv_apply_val] at h1
  have hn : 0 < n := (edgeOf G e).1.pos
  have hv := (edgeOf G e).2.isLt
  constructor
  · rw [h1, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hv, zero_add]
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- The adjacency matrix of a graph decoded from `x` is the matrix read from `x` (the
hypothesis of `map_edgeList` for `decGraph`). -/
theorem decGraph_apply (x : List Bool) (u v : Fin (decGraph x).1) :
    (decGraph x).2 u v = x.getD (finProdFinEquiv (u, v)) false := rfl

/-- Re-encoding the graph decoded from `x` truncates `x` to its first `n²` bits, `n = √|x|`. -/
theorem encGraph_decGraph_eq_take (x : List Bool) :
    encGraph (decGraph x).2 = x.take ((decGraph x).1 * (decGraph x).1) := by
  apply List.ext_getElem
  · rw [length_encGraph, List.length_take,
      min_eq_left (show (decGraph x).1 * (decGraph x).1 ≤ x.length from Nat.sqrt_le _)]
  · intro i h1 h2
    have hi : i < x.length := by
      rw [List.length_take] at h2
      omega
    rw [List.getElem_take]
    simp only [encGraph, List.getElem_ofFn]
    show x.getD (finProdFinEquiv (finProdFinEquiv.symm ⟨i, _⟩)) false = x[i]
    rw [Equiv.apply_symm_apply, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]

/-! ### The numeric model of the samplers -/

/-- The number read (most significant bit first) from the `k` bits of `s` at positions
`b, …, b + k - 1` (default `false`): the loop value of `bitsToNat` on a tape window. -/
def natOfBits (s : List Bool) (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * natOfBits s b j + (s.getD (b + j) false).toNat

@[simp] theorem natOfBits_zero (s : List Bool) (b : ℕ) : natOfBits s b 0 = 0 := rfl

@[simp] theorem natOfBits_succ (s : List Bool) (b j : ℕ) :
    natOfBits s b (j + 1) = 2 * natOfBits s b j + (s.getD (b + j) false).toNat := rfl

/-- A `k`-bit window reads as a number below `2^k`. -/
theorem natOfBits_lt (s : List Bool) (b : ℕ) : ∀ k, natOfBits s b k < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [natOfBits_succ, pow_succ]
    have := natOfBits_lt s b k
    have := Bool.toNat_le (s.getD (b + k) false)
    omega

/-- `bitsToNat` of a tape window is `natOfBits` (`List.ofFn_succ_last`, `List.foldl_append`). -/
theorem bitsToNat_eq_natOfBits (s : List Bool) (b : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => s.getD (b + j) false) = natOfBits s b k
  | 0 => rfl
  | k + 1 => by
    have ih := bitsToNat_eq_natOfBits s b k
    unfold bitsToNat at ih ⊢
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc]
    rw [ih, natOfBits_succ]
    show (2 * natOfBits s b k + if s.getD (b + k) false = true then 1 else 0) =
      2 * natOfBits s b k + (s.getD (b + k) false).toNat
    cases s.getD (b + k) false <;> rfl

/-- **Reading a window as a number is polynomial-time** when `2^k` is polynomially bounded:
a counted loop doubling the accumulator and adding the next bit (`polyTimeComputable_loopState'`,
states `1^{natOfBits} < 1^{2^k}`). -/
theorem natOfBits_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {b : List Bool → ℕ} (hb : PolyTimeComputable fun z => List.replicate (b z) true)
    {k : List Bool → ℕ} (hk : PolyTimeComputable fun z => List.replicate (k z) true)
    (Bd : PolyExpr) (hBd : ∀ z, 2 ^ k z ≤ Bd.eval z.length) :
    PolyTimeComputable fun z => List.replicate (natOfBits (s z) (b z) (k z)) true := by
  let upd : List Bool → List Bool := fun w =>
    List.replicate (2 * (pairSndD (pairSndD w)).length +
      ((s (pairFstD w)).getD (b (pairFstD w) + (pairFstD (pairSndD w)).length) false).toNat) true
  have hupd : PolyTimeComputable upd :=
    unaryAdd_poly
      (unaryMul_poly (unaryConst_poly 2)
        (unaryLength_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
      (unaryOfTest_poly (getBit_poly (hs.comp polyTimeComputable_pairFstD)
        (unaryAdd_poly (hb.comp polyTimeComputable_pairFstD)
          (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))))
  have hclosed : ∀ z i, loopState upd (fun _ => []) z i =
      List.replicate (natOfBits (s z) (b z) i) true := by
    intro z i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [loopState_succ, ih]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        natOfBits_succ]
  have h := polyTimeComputable_loopState' hupd (polyTimeComputable_const []) hk Bd
    fun z i hi => by
      rw [hclosed, List.length_replicate]
      exact ((natOfBits_lt _ _ _).le.trans (Nat.pow_le_pow_right (by norm_num) hi)).trans (hBd z)
  convert h using 1
  funext z
  rw [hclosed]

/-- `List.findSome?` over `finRange T` of a test-and-value function returns the value at the
first accepted index (`firstIdx`), `none` if no index below `T` is accepted. -/
theorem findSome?_finRange_eq {α : Type*} {T : ℕ} (f : Fin T → Option α) (q : ℕ → Bool)
    (v : ℕ → α) (hf : ∀ t : Fin T, f t = if q t then some (v t) else none) :
    (List.finRange T).findSome? f =
      if firstIdx q T < T then some (v (firstIdx q T)) else none := by
  by_cases h : firstIdx q T < T
  · rw [if_pos h, List.findSome?_eq_some_iff]
    refine ⟨(List.finRange T).take (firstIdx q T), ⟨firstIdx q T, h⟩,
      (List.finRange T).drop (firstIdx q T + 1), ?_, ?_, ?_⟩
    · conv_lhs => rw [← List.take_append_drop (firstIdx q T) (List.finRange T)]
      congr 1
      rw [List.drop_eq_getElem_cons (by simpa using h)]
      simp
    · rw [hf, if_pos (q_firstIdx h)]
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 ha
      rw [hf]
      have hlt : ((List.finRange T)[i] : ℕ) < firstIdx q T := by
        simp only [List.getElem_finRange, Fin.cast_mk]
        exact lt_of_lt_of_le hi (min_le_left _ _)
      rw [if_neg (by simpa using firstIdx_min hlt)]
  · rw [if_neg h, List.findSome?_eq_none_iff]
    intro t _
    rw [hf]
    have hT : firstIdx q T = T := le_antisymm firstIdx_le (not_lt.1 h)
    rw [if_neg (by simpa using firstIdx_eq_iff.1 hT t t.isLt)]

/-- The index of the first accepted trial of `T` rejection trials of `k` bits on the tape `s`
(a value below `m` is accepted), `T` if none is accepted. -/
noncomputable def firstTrial (s : List Bool) (m k T : ℕ) : ℕ :=
  firstIdx (fun t => decide (natOfBits s (t * k) k < m)) T

/-- The value of the rejection sampler as a number, with default `d` on failure. -/
noncomputable def sampleVal (s : List Bool) (m k T d : ℕ) : ℕ :=
  if firstTrial s m k T < T then natOfBits s (firstTrial s m k T * k) k else d

/-- The rejection sampler of `Language.lean`, numerically: the value read at the first accepted
trial. -/
theorem map_val_sampleIdx (m k T : ℕ) (s : List Bool) :
    (sampleIdx m k T s).map Fin.val =
      if firstTrial s m k T < T then some (natOfBits s (firstTrial s m k T * k) k) else none := by
  unfold sampleIdx rejectionSample
  rw [List.map_findSome?]
  apply findSome?_finRange_eq (q := fun t => decide (natOfBits s (t * k) k < m))
    (v := fun t => natOfBits s (t * k) k)
  intro t
  simp only [Function.comp, uniformFromBits, bitsToNat_eq_natOfBits]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simpa using h2)
  · exact absurd (by simpa using h2) h1
  · rfl

/-- The total rejection sampler with default `d` is `sampleVal`. -/
theorem map_val_sampleIdx_getD (m k T : ℕ) (s : List Bool) (d : ℕ) :
    ((sampleIdx m k T s).map Fin.val).getD d = sampleVal s m k T d := by
  rw [map_val_sampleIdx]
  unfold sampleVal
  split_ifs <;> rfl

/-- **The rejection sampler is polynomial-time** (in unary, when `2^k` is polynomially
bounded): the first accepted trial by `polyTimeComputable_firstIdx` with the window test
`natOfBits_poly`, then the value at that trial. -/
theorem sampleVal_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {m : List Bool → ℕ} (hm : PolyTimeComputable fun z => List.replicate (m z) true)
    {k : List Bool → ℕ} (hk : PolyTimeComputable fun z => List.replicate (k z) true)
    {T : List Bool → ℕ} (hT : PolyTimeComputable fun z => List.replicate (T z) true)
    {d : List Bool → ℕ} (hd : PolyTimeComputable fun z => List.replicate (d z) true)
    (Bd : PolyExpr) (hBd : ∀ z, 2 ^ k z ≤ Bd.eval z.length) :
    PolyTimeComputable fun z => List.replicate (sampleVal (s z) (m z) (k z) (T z) (d z)) true := by
  have hBd' : ∀ w : List Bool, 2 ^ k (pairSndD w) ≤ Bd.eval w.length := fun w =>
    (hBd _).trans (Bd.eval_mono
      ((Nat.le_add_left _ _).trans (length_pairFstD_add_pairSndD_le w)))
  have hwin : PolyTimeComputable fun w =>
      List.replicate (natOfBits (s (pairSndD w)) ((pairFstD w).length * k (pairSndD w))
        (k (pairSndD w))) true :=
    natOfBits_poly (hs.comp polyTimeComputable_pairSndD)
      (unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD)
        (hk.comp polyTimeComputable_pairSndD))
      (hk.comp polyTimeComputable_pairSndD) Bd hBd'
  have hfirst : PolyTimeComputable fun z =>
      List.replicate (firstTrial (s z) (m z) (k z) (T z)) true :=
    polyTimeComputable_firstIdx (p := fun z t => decide (natOfBits (s z) (t * k z) (k z) < m z))
      (ltTest_poly hwin (hm.comp polyTimeComputable_pairSndD)) hT
  have hval : PolyTimeComputable fun z =>
      List.replicate (natOfBits (s z) (firstTrial (s z) (m z) (k z) (T z) * k z) (k z)) true :=
    natOfBits_poly hs (unaryMul_poly hfirst hk) hk Bd hBd
  convert polyTimeComputable_ite (ltTest_poly hfirst hT) hval hd using 1
  funext z
  simp only [decide_eq_true_eq]
  unfold sampleVal
  split_ifs <;> rfl

/-! ### The colour permutation as a table -/

/-- The six-bit table of a colour permutation: the encodings of the images of the three
colours. -/
def permTable (σ : Equiv.Perm (Fin 3)) : List Bool :=
  encColor (σ 0) ++ encColor (σ 1) ++ encColor (σ 2)

/-- The table of the permutation of index `i < 6` under `perm3Equiv`, the identity's table for
`i ≥ 6` (the sampler's failure value). -/
noncomputable def tableOfIdx (i : ℕ) : List Bool :=
  if i = 0 then permTable (perm3Equiv 0) else if i = 1 then permTable (perm3Equiv 1) else
  if i = 2 then permTable (perm3Equiv 2) else if i = 3 then permTable (perm3Equiv 3) else
  if i = 4 then permTable (perm3Equiv 4) else if i = 5 then permTable (perm3Equiv 5) else
  permTable 1

/-- On the indices below `6` the table lookup is the table of `perm3Equiv`. -/
theorem tableOfIdx_perm3Equiv (i : Fin 6) : tableOfIdx i = permTable (perm3Equiv i) := by
  fin_cases i <;> simp [tableOfIdx]

/-- The honest prover's permutation table is the table lookup on the sampled index (default
`6`, the identity). -/
theorem permTable_samplePerm3 (T : ℕ) (s : List Bool) :
    permTable (samplePerm3 T s) = tableOfIdx (sampleVal s 6 3 T 6) := by
  rw [← map_val_sampleIdx_getD]
  unfold samplePerm3
  cases sampleIdx 6 3 T s with
  | none => simp [tableOfIdx]
  | some i =>
    simp only [Option.map_some, Option.getD_some]
    exact (tableOfIdx_perm3Equiv i).symm

/-- The table lookup is polynomial-time (seven constant tables selected by equality tests on
the unary index). -/
theorem tableOfIdx_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun z => List.replicate (f z) true) :
    PolyTimeComputable fun z => tableOfIdx (f z) := by
  have t : ∀ c : ℕ, PolyTimeComputable fun z => [decide (f z = c)] := fun c =>
    eqTest_poly hf (unaryConst_poly c)
  convert polyTimeComputable_ite (t 0) (polyTimeComputable_const (permTable (perm3Equiv 0)))
    (polyTimeComputable_ite (t 1) (polyTimeComputable_const (permTable (perm3Equiv 1)))
      (polyTimeComputable_ite (t 2) (polyTimeComputable_const (permTable (perm3Equiv 2)))
        (polyTimeComputable_ite (t 3) (polyTimeComputable_const (permTable (perm3Equiv 3)))
          (polyTimeComputable_ite (t 4) (polyTimeComputable_const (permTable (perm3Equiv 4)))
            (polyTimeComputable_ite (t 5) (polyTimeComputable_const (permTable (perm3Equiv 5)))
              (polyTimeComputable_const (permTable 1))))))) using 1
  funext z
  simp [tableOfIdx]

/-- The two bits of a table at colour `a`: bits `2a` and `2a + 1`. -/
def colorFromTable (tbl : List Bool) (a : ℕ) : List Bool :=
  [tbl.getD (2 * a) false, tbl.getD (2 * a + 1) false]

/-- The encoding of a colour, numerically: `[a / 2 = 1, a % 2 = 1]`. -/
theorem encColor_eq (a : Fin 3) : encColor a = [decide (a.val / 2 = 1), decide (a.val % 2 = 1)] := by
  fin_cases a <;> rfl

/-- Looking up colour `a` in the table of `σ` gives the encoding of `σ a`. -/
theorem colorFromTable_permTable (σ : Equiv.Perm (Fin 3)) (a : Fin 3) :
    colorFromTable (permTable σ) a = encColor (σ a) := by
  fin_cases a <;> simp [colorFromTable, permTable, encColor_eq]

/-- The table lookup of a colour is polynomial-time (two bit extractions). -/
theorem colorFromTable_poly {tbl : List Bool → List Bool} (htbl : PolyTimeComputable tbl)
    {a : List Bool → ℕ} (ha : PolyTimeComputable fun z => List.replicate (a z) true) :
    PolyTimeComputable fun z => colorFromTable (tbl z) (a z) :=
  ptc_congr ((getBit_poly htbl (unaryMul_poly (unaryConst_poly 2) ha)).append
    (getBit_poly htbl (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) ha) (unaryConst_poly 1))))
    fun _ => rfl

/-! ### Colours as numbers -/

/-- The colour of vertex `u` read from an encoded colouring: `(2 b₀ + b₁) mod 3` from bits
`2u`, `2u + 1`. -/
def colorVal (y : List Bool) (u : ℕ) : ℕ :=
  (2 * (y.getD (2 * u) false).toNat + (y.getD (2 * u + 1) false).toNat) % 3

/-- `decColoring` numerically. -/
theorem decColoring_val (n : ℕ) (y : List Bool) (u : Fin n) :
    ((decColoring n y u : Fin 3) : ℕ) = colorVal y u := by
  have h0 : ((finProdFinEquiv (u, (0 : Fin 2)) : Fin (n * 2)) : ℕ) = 2 * u := by
    rw [finProdFinEquiv_apply_val]
    simp
  have h1 : ((finProdFinEquiv (u, (1 : Fin 2)) : Fin (n * 2)) : ℕ) = 2 * u + 1 := by
    rw [finProdFinEquiv_apply_val]
    simp
    omega
  show (2 * (y.getD (finProdFinEquiv (u, (0 : Fin 2))) false).toNat +
    (y.getD (finProdFinEquiv (u, (1 : Fin 2))) false).toNat) % 3 = _
  rw [h0, h1]
  rfl

/-- `decColor` numerically. -/
theorem decColor_val (w : List Bool) : ((decColor w : Fin 3) : ℕ) = colorVal w 0 := by
  rw [decColor, decColoring_val]
  rfl

/-- The colour value of a vertex is polynomial-time in unary. -/
theorem colorVal_poly {y : List Bool → List Bool} (hy : PolyTimeComputable y)
    {u : List Bool → ℕ} (hu : PolyTimeComputable fun z => List.replicate (u z) true) :
    PolyTimeComputable fun z => List.replicate (colorVal (y z) (u z)) true := by
  have h2u := unaryMul_poly (unaryConst_poly 2) hu
  have h := modNum_poly
    (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) (unaryOfTest_poly (getBit_poly hy h2u)))
      (unaryOfTest_poly (getBit_poly hy (unaryAdd_poly h2u (unaryConst_poly 1)))))
    (unaryConst_poly 3)
  convert h using 1
  funext z
  rw [modNum_eq]
  rfl

/-- The encoding of a colour from its value: `[a / 2 = 1, a % 2 = 1]`. -/
def encColorOfVal (a : ℕ) : List Bool := [decide (a / 2 = 1), decide (a % 2 = 1)]

/-- `encColor` is `encColorOfVal` of the colour's value. -/
theorem encColor_eq_ofVal (a : Fin 3) : encColor a = encColorOfVal a := encColor_eq a

/-- The colour encoding from a unary value is polynomial-time. -/
theorem encColorOfVal_poly {a : List Bool → ℕ}
    (ha : PolyTimeComputable fun z => List.replicate (a z) true) :
    PolyTimeComputable fun z => encColorOfVal (a z) := by
  have h1 := eqTest_poly (divNum_poly ha (unaryConst_poly 2)) (unaryConst_poly 1)
  have h2 := eqTest_poly (modNum_poly ha (unaryConst_poly 2)) (unaryConst_poly 1)
  convert h1.append h2 using 1
  funext z
  simp [encColorOfVal, divNum_eq, modNum_eq]

/-! ### Message encodings -/

/-- A pair is the pair with empty second component followed by the second component. -/
theorem pairEncode_eq_append_nil (a b : List Bool) : pairEncode a b = pairEncode a [] ++ b := by
  simp [pairEncode]

/-- An encoded message list is the concatenation of the self-delimiting messages
`pairEncode m []`. -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap (fun m => pairEncode m []) := by
  induction l with
  | nil => rfl
  | cons m h ih => rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ih, pairEncode_eq_append_nil]

/-- `List.ofFn f` is the image of `range n` under any `ℕ`-indexed extension of `f`. -/
theorem ofFn_eq_map_range {α : Type*} {n : ℕ} (f : Fin n → α) (F : ℕ → α)
    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) : List.ofFn f = (List.range n).map F := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact h i (by simpa using h1)

/-- The `i`-th second projection of an encoded history drops its first `i` messages. -/
theorem iterate_pairSndD_encodeMsgs (hist : List (List Bool)) :
    ∀ i, pairSndD^[i] (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop i) := by
  intro i
  induction i generalizing hist with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases hist with
    | nil =>
      show pairSndD^[i] [] = []
      exact Function.iterate_fixed rfl i
    | cons m h => rw [Strategy.encodeMsgs_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]

/-- An encoded history is empty iff the history is. -/
theorem encodeMsgs_eq_nil_iff (hist : List (List Bool)) :
    Strategy.encodeMsgs hist = [] ↔ hist = [] := by
  cases hist with
  | nil => simp
  | cons m h => simp [pairEncode]

/-- A history is no longer than its encoding. -/
theorem length_le_length_encodeMsgs (hist : List (List Bool)) :
    hist.length ≤ (Strategy.encodeMsgs hist).length := by
  induction hist with
  | nil => exact le_rfl
  | cons m h ih =>
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons]
    omega

/-- The `i`-th message of a history (default `[]`) is the first projection after `i` second
projections of its encoding (`Strategy.pairFstD_encodeMsgs`). -/
theorem getD_eq_pairFstD_iterate (hist : List (List Bool)) (i : ℕ) :
    hist.getD i [] = pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) := by
  rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD]

/-- The last message of a history (default `[]`) is its message of index `length - 1`. -/
theorem getLastD_eq_getD (hist : List (List Bool)) : hist.getLastD [] = hist.getD (hist.length - 1) [] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The number of messages of an encoded history: the number of second projections needed to
reach the empty word, searched below `|M| + 1`. -/
noncomputable def histLen (M : List Bool) : ℕ :=
  firstIdx (fun i => decide (pairSndD^[i] M = [])) (M.length + 1)

/-- `histLen` recovers the length of the history. -/
theorem histLen_encodeMsgs (hist : List (List Bool)) :
    histLen (Strategy.encodeMsgs hist) = hist.length := by
  unfold histLen
  apply firstIdx_eq_of
  · exact Nat.lt_succ_of_le (length_le_length_encodeMsgs hist)
  · rw [iterate_pairSndD_encodeMsgs, List.drop_length]
    simp
  · intro i hi
    rw [iterate_pairSndD_encodeMsgs, decide_eq_false_iff_not, encodeMsgs_eq_nil_iff,
      ← List.length_eq_zero_iff, List.length_drop]
    omega

/-- The message count of an encoded history is polynomial-time in unary. -/
theorem histLen_poly : PolyTimeComputable fun M => List.replicate (histLen M) true :=
  polyTimeComputable_firstIdx (p := fun M i => decide (pairSndD^[i] M = []))
    (isNil_poly.comp (iterSnd_poly polyTimeComputable_pairSndD
      (unaryLength_poly polyTimeComputable_pairFstD)))
    (unaryAdd_poly (unaryLength_poly polyTimeComputable_id) (unaryConst_poly 1))

/-- A pair is never the empty word. -/
theorem pairEncode_ne_nil (a b : List Bool) : pairEncode a b ≠ [] := by
  simp [pairEncode]

/-- An encoded `ofFn` list is the concatenation of the self-delimiting messages
`pairEncode (F i) []` over `i < n`, for any `ℕ`-indexed extension `F` of `f`. -/
theorem encodeMsgs_ofFn_eq_flatMap {n : ℕ} (f : Fin n → List Bool) (F : ℕ → List Bool)
    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) :
    Strategy.encodeMsgs (List.ofFn f) = (List.range n).flatMap (fun i => pairEncode (F i) []) := by
  rw [ofFn_eq_map_range f F h, encodeMsgs_eq_flatMap, List.flatMap_map]

/-- With at least one edge, `edgeAt G e` is the edge of index `e mod |E|`. -/
theorem edgeAt_eq_some_of_pos {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :
    edgeAt G e = some (edgeOf G ⟨e % edgeCount G, Nat.mod_lt _ hm⟩) := by
  unfold edgeAt
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hm)]
  rfl

end TCSlib.Cryptography.ColMachines
