/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Cryptography.SecureComputation.Compose
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time machines on encoded histories

The machine infrastructure behind the efficiency of the composed parties
(`HybridProtocol.composeP_efficient`, `composeV_efficient`) [Gol04, §7.3.1, the protocol of
Theorem 7.3.3]: a party of `H.compose ρ` reads its history `encodeMsgs hist` at interleaved
positions (the messages of one run of `ρ` sit at every other pair, `Compose.slotMsgs`), and maps
`ρ`'s next-message function over the `L(n)` runs. Both are loops over a data-dependent range of
the unary FP toolkit (`ZeroKnowledge/EncodingMachines.lean`) and the peeling loops of
`GraphIsomorphism/EfficiencyRep.lean`.

## Main definitions

* `ComposeMachines.padTo`: zero padding, the string form of `padFin`.

## Main results

* `ComposeMachines.polyTimeComputable_flatMap_range`: concatenating a polynomial-time chunk over
  a data-dependent range is polynomial-time.
* `ComposeMachines.iterSnd_poly`, `msgAt_encodeMsgs`: the `i`-th message of an encoded history.
* `ComposeMachines.encodeMsgs_append`, `encodeMsgs_eq_flatMap`, `encodeMsgs_slotMsgs`: the
  history encoding as a concatenation of chunks, and the interleaved slots of a history.
* `ComposeMachines.polyTimeComputable_slots`: **the interleaved-slot map**: the encoded messages
  `slotMsgs sel off p hist` are a polynomial-time function of the encoded history, for a
  polynomial-time selector and unary offset and count.
* `ComposeMachines.Efficient.exists_polyTime`: an efficient strategy's next-message function is
  a polynomial-time function of the machine layout `GI.ilayout` (the converse of
  `GI.efficient_of_polyTime`).
* `ComposeMachines.ofFn_padFin`, `padTo_poly`: `padFin` as a polynomial-time string map.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines and their time complexity, pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### Loops over a data-dependent range -/

/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
`E i` over `i < min N L`:
`(range N).flatMap (fun i => if i < L then E i else []) = (range (min N L)).flatMap E`. -/
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

/-- **Concatenating a chunk over a data-dependent range**: if the chunk `E z i` is a
polynomial-time function of `⟨1^i, z⟩` and the count `n z` is a unary function, then
`z ↦ E z 0 ++ ⋯ ++ E z (n z − 1)` is polynomial-time.
`PolyTimeComputable fun z => (List.range (n z)).flatMap (E z)`.

**Proof sketch.** An instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
`EncodingMachines.cstep` from `⟨[], z⟩`, whose `i`-th iterate is `⟨1^i, z⟩` (`cstep_iterate`),
emitting `E z i` while `i < n z` (`flatMap_range_ite`); the number of rounds is the polynomial
bound of the unary count (`PolyTimeComputable.output_length_le`). -/
theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
  obtain ⟨C, c, hC⟩ := hn.output_length_le
  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
      (hn.comp polyTimeComputable_pairSndD)
  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  refine (hL.comp hpre).congr fun z => ?_
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]

/-! ### Reading an encoded history -/

/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
polynomial-time `s` and a unary count `i`.
`PolyTimeComputable fun z => pairSndD^[i z] (s z)`.

**Proof sketch.** `GI.iterUnary_poly` with the step `⟨x₀, s⟩ ↦ pairSndD s` on
`⟨1^{i z}, s z⟩`; peeling never lengthens a word (`GI.length_iterate_le`,
`GI.length_pairSndD_le`), so the orbit is bounded by the input length. -/
theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
  have hstep : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hclosed : ∀ x₀ k, (fun t => pairSndD (pairSndD (pairEncode x₀ t)))^[k] (pairSndD x₀) =
      pairSndD^[k] (pairSndD x₀) := by
    intro x₀ k
    congr 1
    funext t
    rw [pairSndD_pairEncode]
  have hit := GI.iterUnary_poly hstep .var fun x₀ k _ => by
    rw [hclosed, PolyExpr.eval_var]
    exact (GI.length_iterate_le GI.length_pairSndD_le _ k).trans (GI.length_pairSndD_le x₀)
  refine (hit.comp (hi.pairEncode hs)).congr fun z => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- **The `i`-th message of an encoded history**: `pairFstD (pairSndD^[i] (encodeMsgs hist)) =
hist.getD i []` (`GI.iterate_pairSndD_encodeMsgs`, `Strategy.pairFstD_encodeMsgs`). -/
theorem msgAt_encodeMsgs (hist : List (List Bool)) (i : ℕ) :
    pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) = hist.getD i [] := by
  rw [GI.iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD]

/-- **The history encoding is a concatenation**:
`encodeMsgs (a ++ b) = encodeMsgs a ++ encodeMsgs b` (`pairEncode_nil_append`).
It is the public `CommitmentLemmas.encodeMsgs_append` (`ZeroKnowledge/CommitmentLemmas.lean`). -/
theorem encodeMsgs_append (a b : List (List Bool)) :
    Strategy.encodeMsgs (a ++ b) = Strategy.encodeMsgs a ++ Strategy.encodeMsgs b :=
  TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append a b

/-- **The history encoding chunk by chunk**: `encodeMsgs l = l.flatMap fun m => ⟨m, []⟩`. -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
  induction l with
  | nil => rw [Strategy.encodeMsgs_nil, List.flatMap_nil]
  | cons m l ih =>
    rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ← ih, BinArith.pairEncode_nil_append]

/-- **The encoded slots of a history**: the encoding of `slotMsgs sel off p hist` is the
concatenation over `q < p` of the chunk `⟨hist[off + q], []⟩` when `sel q`, read from the
encoded history (`msgAt_encodeMsgs`):
`encodeMsgs (slotMsgs sel off p hist) = (range p).flatMap fun q =>
if sel q then ⟨pairFstD (pairSndD^[off + q] (encodeMsgs hist)), []⟩ else []`. -/
theorem encodeMsgs_slotMsgs (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) :
    Strategy.encodeMsgs (Compose.slotMsgs sel off p hist) =
      (List.range p).flatMap fun q =>
        if sel q then pairEncode (pairFstD (pairSndD^[off + q] (Strategy.encodeMsgs hist))) []
        else [] := by
  rw [Compose.slotMsgs_eq, encodeMsgs_eq_flatMap, List.flatMap_map]
  induction p with
  | zero => simp only [List.range_zero, List.filter_nil, List.flatMap_nil]
  | succ p ih =>
    rw [List.range_succ, List.filter_append, List.flatMap_append, List.flatMap_append, ih,
      List.flatMap_singleton]
    congr 1
    cases h : sel p
    · rw [List.filter_singleton, h, cond_false, List.flatMap_nil, if_neg Bool.false_ne_true]
    · rw [List.filter_singleton, h, cond_true, List.flatMap_singleton, if_pos rfl,
        msgAt_encodeMsgs]

/-- **The interleaved-slot map**: for a selector `sel z q` that is a polynomial-time test of
`⟨1^q, z⟩`, unary offset `off z` and count `p z`, and a polynomial-time word `M z`, the word
`(range (p z)).flatMap fun q => if sel z q then ⟨pairFstD (pairSndD^[off z + q] (M z)), []⟩
else []` is polynomial-time; on `M z = encodeMsgs hist` it is
`encodeMsgs (slotMsgs (sel z) (off z) (p z) hist)` (`encodeMsgs_slotMsgs`).

**Proof sketch.** `polyTimeComputable_flatMap_range` with the chunk built from the test, the
iterated projection at the unary count `off z + q` (`iterSnd_poly`, `unaryAdd_poly`) and
`pairEncode`. -/
theorem polyTimeComputable_slots {sel : List Bool → ℕ → Bool}
    (hsel : PolyTimeComputable fun w => [sel (pairSndD w) (pairFstD w).length])
    {off p : List Bool → ℕ} (hoff : PolyTimeComputable fun z => List.replicate (off z) true)
    (hp : PolyTimeComputable fun z => List.replicate (p z) true)
    {M : List Bool → List Bool} (hM : PolyTimeComputable M) :
    PolyTimeComputable fun z => (List.range (p z)).flatMap fun q =>
      if sel z q then pairEncode (pairFstD (pairSndD^[off z + q] (M z))) [] else [] := by
  have hcnt : PolyTimeComputable fun w =>
      List.replicate (off (pairSndD w) + (pairFstD w).length) true :=
    unaryAdd_poly (hoff.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have hmsg := polyTimeComputable_pairFstD.comp
    (iterSnd_poly (hM.comp polyTimeComputable_pairSndD) hcnt)
  exact polyTimeComputable_flatMap_range
    (polyTimeComputable_ite hsel (hmsg.pairEncode (polyTimeComputable_const []))
      (polyTimeComputable_const [])) hp

/-! ### Strategies as functions of the machine layout -/

/-- **An efficient strategy is a polynomial-time function of the layout** (the converse of
`GI.efficient_of_polyTime`): if `S.Efficient`, there is a polynomial-time `F` with
`S.next x z r hist = F (GI.ilayout x z hist r)` (the output
function of the uniform machine, `NUPPT.polyTimeComputable_output`; its advice is empty). -/
theorem Efficient.exists_polyTime {S : Strategy} (h : S.Efficient) :
    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ x z r hist, S.next x z r hist = F (GI.ilayout x z hist r) := by
  obtain ⟨A, hA, -, hnext⟩ := (Strategy.efficient_iff S).1 h
  refine ⟨A.output, A.polyTimeComputable_output, fun x z r hist => ?_⟩
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA,
    GI.ilayout_def]

/-! ### Zero padding -/

/-- **Zero padding** to length `L` (and truncation to `L`): `padTo L w = (w ++ 0^L).take L`, the
string form of `padFin L w` (`ofFn_padFin`). -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- The defining equation of `padTo`: `padTo L w = (w ++ 0^L).take L`. -/
theorem padTo_eq (L : ℕ) (w : List Bool) : padTo L w = (w ++ List.replicate L false).take L :=
  rfl

/-- Padding to a unary length is polynomial-time (`EncodingMachines.truncate_poly`, the zeros
`GI.zeros_poly` of the unary string).
`PolyTimeComputable fun x => padTo (L x) (s x)`. -/
theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => padTo (L x) (s x) :=
  truncate_poly (hs.append ((GI.zeros_poly.comp' hL).congr fun x => by
    rw [List.length_replicate])) hL

/-- The padded word has length `L`: `|padTo L w| = L`. -/
theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
  rw [padTo_eq, List.length_take, List.length_append, List.length_replicate]
  omega

/-- **`padFin` as a string**: `List.ofFn (padFin L w) = padTo L w`. -/
theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_ofFn, padTo_eq, List.getElem?_take]
  by_cases hi : i < L
  · rw [dif_pos hi, if_pos hi, padFin_apply, Fin.val_mk, List.getD_eq_getElem?_getD,
      List.getElem?_append]
    split_ifs with h
    · rw [List.getElem?_eq_getElem h, Option.getD_some]
    · rw [List.getElem?_eq_none_iff.2 (by omega), Option.getD_none,
        List.getElem?_replicate, if_pos (by omega)]
  · rw [dif_neg hi, if_neg hi]

end TCSlib.Cryptography.SecureComputation.ComposeMachines
