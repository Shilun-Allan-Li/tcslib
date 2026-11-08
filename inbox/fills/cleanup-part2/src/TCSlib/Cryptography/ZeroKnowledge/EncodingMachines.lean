/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Find

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time machines for the string encodings of the graph protocols

The machine infrastructure behind the three polynomial-time statements of
`TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` (Inf-4.2: applying an encoded permutation to
an encoded graph, composing encoded permutations, sampling a permutation from coins). All of
it is built from the proved machine layer of `TCSlib/Complexity/Randomized/` — the
repetition lemma `Complexity.polyTimeComputable_iterateFind`, its emitting variant
`Complexity.polyTimeComputable_iterateEmit`, the typed cuts `pairTakePoly`/`pairDropPoly`, the
unary multiplication machine and the FP toolkit of `Build/StateLoop.lean` — and never touches
a machine directly.

The organising idea is that **numbers travel in unary** (`1^m = List.replicate m true`): a
"unary function" is a map `x ↦ 1^{f x}` with `f : List Bool → ℕ`, and the toolkit closes the
unary functions under addition, multiplication, truncated subtraction, polynomial evaluation,
comparison tests, bit extraction (`getD`), bounded first-index search (`firstIdx`), counted
loops, division and `Nat.sqrt`. The **bit-extraction principle** `polyTimeComputable_of_getD` then says that a
string function `F` is polynomial-time as soon as its length `|F z|` is a unary function and
its `m`-th bit `(F z).getD m false` is a polynomial-time test of `⟨1^m, z⟩`; the adjacency and
relation matrices of the graph protocols are produced bit by bit through it. The file is
independent of the encodings themselves (which import it), so that
`ZeroKnowledge/Encoding.lean` only has to identify the bits of its matrices with the numeric
functions proved polynomial-time here.

## Main definitions

* `TCSlib.Cryptography.EncodingMachines.firstIdx` — the least index `i < n` accepted by a
  test, or `n` when there is none.
* `TCSlib.Cryptography.EncodingMachines.cstep` — the unary counter step `⟨c, z⟩ ↦ ⟨1 :: c, z⟩`
  driving the searches and the bit-emitting loops.
* `TCSlib.Cryptography.EncodingMachines.loopState` — the state of a counted loop
  (`s ↦ upd ⟨x, ⟨1^i, s⟩⟩` from `init x`).
* `TCSlib.Cryptography.EncodingMachines.divNum`, `modNum` — Euclidean division as a bounded
  search.

## Main results

* `TCSlib.Cryptography.EncodingMachines.unaryAdd_poly`, `unaryMul_poly`, `unarySub_poly`,
  `unaryPolyOf_poly`, `leTest_poly`, `ltTest_poly`, `eqTest_poly`, `unaryMin_poly`,
  `getBit_poly` — the unary toolkit.
* `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_firstIdx` — bounded first-index
  search is polynomial-time (an instance of the repetition lemma).
* `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_of_getD` — the bit-extraction
  principle (an instance of `Complexity.polyTimeComputable_iterateEmit`).
* `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_loopState` — counted loops with
  self-bounded updates are polynomial-time (a state loop).
* `TCSlib.Cryptography.EncodingMachines.unarySqrt_poly`, `divNum_poly`, `modNum_poly`,
  `unarySize_poly` — `Nat.sqrt`, division, remainder and `Nat.size` in unary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6; §4.7 Protocol 127.5.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 1, string encodings of combinatorial objects; §2.2, FP.)
-/

namespace TCSlib.Cryptography.EncodingMachines

open Complexity Turing Complexity.StateLoop

/-! ### Unary arithmetic -/

/-- The sum of two unary functions is a unary function (concatenate the two unary strings,
`List.replicate_add`). -/
theorem unaryAdd_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x + g x) true := by
  simpa only [List.replicate_add] using hf.append hg

/-- The product of two unary functions is a unary function: pair the two unary strings and
apply the unary-multiplication machine `Turing.FinTM.computesFunInTime_unaryMul` (a copy of the
private `Complexity.polyTimeComputable_unaryMulFun` of `Randomized/Primitives.lean`). -/
theorem unaryMul_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x * g x) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have hmul : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert hmul.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- The truncated difference of two unary functions is a unary function: drop `g x` tokens
from `1^{f x}` (`Complexity.polyTimeComputable_pairDropPoly` at the variable length,
`List.drop_replicate`). -/
theorem unarySub_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x - g x) true := by
  convert (polyTimeComputable_pairDropPoly .var).comp (hg.pairEncode hf) using 1
  funext x
  simp [List.drop_replicate]

/-- A constant is a unary function. -/
theorem unaryConst_poly (c : ℕ) :
    PolyTimeComputable fun _ : List Bool => List.replicate c true :=
  polyTimeComputable_const _

/-- The length of a polynomial-time string function is a unary function
(`Complexity.polyTimeComputable_unary`). -/
theorem unaryLength_poly {h : List Bool → List Bool} (hh : PolyTimeComputable h) :
    PolyTimeComputable fun x => List.replicate (h x).length true :=
  polyTimeComputable_unary.comp hh

/-- A syntactic polynomial of a unary function is a unary function
(`Complexity.polyTimeComputable_unaryPoly` after the unary string). -/
theorem unaryPolyOf_poly (p : PolyExpr) {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => List.replicate (p.eval (f x)) true := by
  convert (polyTimeComputable_unaryPoly p).comp hf using 1
  funext x
  simp

/-- The comparison `f x ≤ g x` of two unary functions is a polynomial-time test
(`Complexity.StateLoop.lenLe_comp`). -/
theorem leTest_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => [decide (f x ≤ g x)] := by
  convert lenLe_comp hg hf using 1
  funext x
  simp

/-- The strict comparison `f x < g x` of two unary functions is a polynomial-time test
(`f + 1 ≤ g`). -/
theorem ltTest_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => [decide (f x < g x)] := by
  convert leTest_poly (unaryAdd_poly hf (unaryConst_poly 1)) hg using 1

/-- The equality `f x = g x` of two unary functions is a polynomial-time test
(`Complexity.polyTimeComputable_lenEq` on the pair of unary strings). -/
theorem eqTest_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => [decide (f x = g x)] := by
  convert polyTimeComputable_lenEq.comp (hf.pairEncode hg) using 1
  funext x
  simp

/-- The minimum of two unary functions is a unary function (`Complexity.polyTimeComputable_ite`
on the comparison test). -/
theorem unaryMin_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (min (f x) (g x)) true := by
  convert polyTimeComputable_ite (leTest_poly hf hg) hf hg using 1
  funext x
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left h]
  · rw [min_eq_right (not_le.1 h).le]

/-- Reading bit number `f x` (default `false`) of a polynomial-time string `h x` is a
polynomial-time test: drop `f x` bits (`Complexity.polyTimeComputable_pairDropPoly`) and read
the head (`Complexity.StateLoop.headBit_poly`). -/
theorem getBit_poly {h : List Bool → List Bool} (hh : PolyTimeComputable h) {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => [(h x).getD (f x) false] := by
  convert headBit_poly.comp ((polyTimeComputable_pairDropPoly .var).comp (hf.pairEncode hh))
    using 1
  funext x
  simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The Boolean value of a one-bit test as a unary function: `1^{[b x]}` has length `1` iff the
test holds (`Complexity.polyTimeComputable_ite` between the constants `1^1` and `1^0`). -/
theorem unaryOfTest_poly {b : List Bool → Bool} (hb : PolyTimeComputable fun x => [b x]) :
    PolyTimeComputable fun x => List.replicate (b x).toNat true := by
  convert polyTimeComputable_ite hb (unaryConst_poly 1) (unaryConst_poly 0) using 1
  funext x
  cases b x <;> rfl

/-! ### The unary counter loop -/

/-- The counter step `⟨c, z⟩ ↦ ⟨1 :: c, z⟩` on state words: iterated from `⟨[], z⟩` it
enumerates the words `⟨1^i, z⟩`, the arguments of the searches and bit-emitting loops below. -/
def cstep (w : List Bool) : List Bool := pairEncode (true :: pairFstD w) (pairSndD w)

/-- The counter step is polynomial-time. -/
theorem cstep_poly : PolyTimeComputable cstep :=
  ((cons_poly true).comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD

/-- The closed form of the counter orbit on a state word: `cstep^[i] ⟨c, z⟩ = ⟨1^i ++ c, z⟩`. -/
theorem cstep_iterate (c z : List Bool) (i : ℕ) :
    cstep^[i] (pairEncode c z) = pairEncode (List.replicate i true ++ c) z := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [cstep, List.replicate_succ]

/-- The counter orbit of an arbitrary word `x` stays within `2 i + 2 |x| + 2` after `i` rounds
(`Complexity.StateLoop.length_pairFstD_add_pairSndD_le`). -/
theorem length_cstep_iterate_le (x : List Bool) (i : ℕ) :
    (cstep^[i] x).length ≤ 2 * i + 2 * x.length + 2 := by
  cases i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i =>
    rw [Function.iterate_succ_apply,
      show cstep x = pairEncode (true :: pairFstD x) (pairSndD x) from rfl, cstep_iterate,
      length_pairEncode]
    have := length_pairFstD_add_pairSndD_le x
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega

/-- The orbit polynomial `2 R(n) + 2 n + 2` of the counter loop with round polynomial `R`. -/
def cbound (R : PolyExpr) : PolyExpr :=
  .add (.mul (.const 2) R) (.add (.mul (.const 2) .var) (.const 2))

/-- The orbit hypothesis of the repetition lemma for the counter step: within `R|x|` rounds
the orbit of any word stays within `cbound R`. -/
theorem cstep_horbit (R : PolyExpr) (x : List Bool) (i : ℕ) (hi : i ≤ R.eval x.length) :
    (cstep^[i] x).length ≤ (cbound R).eval x.length := by
  have := length_cstep_iterate_le x i
  simp only [cbound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-! ### Bounded first-index search -/

/-- The least index `i < n` with `q i = true`, or `n` if there is none (the search performed by
the decoders of the graph protocols: the first set bit of a row, the preimage of a vertex, the
first accepted rejection trial). -/
noncomputable def firstIdx (q : ℕ → Bool) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ i < n, q i = true then Nat.find h else n

variable {q : ℕ → Bool} {n : ℕ}

/-- The search index is at most `n`. -/
theorem firstIdx_le : firstIdx q n ≤ n := by
  unfold firstIdx
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- The search index is `N` when `q N` holds, `N < n`, and `q` fails below `N`. -/
theorem firstIdx_eq_of {N : ℕ} (hN : N < n) (hq : q N = true) (hmin : ∀ i < N, q i = false) :
    firstIdx q n = N := by
  unfold firstIdx
  have h : ∃ i < n, q i = true := ⟨N, hN, hq⟩
  rw [dif_pos h]
  exact (Nat.find_eq_iff h).2 ⟨⟨hN, hq⟩, fun i hi hi' => by simp [hmin i hi] at hi'⟩

/-- The search index is `n` when `q` fails on the whole range. -/
theorem firstIdx_eq_of_forall (h : ∀ i < n, q i = false) : firstIdx q n = n := by
  unfold firstIdx
  rw [dif_neg]
  rintro ⟨i, hi, hq⟩
  simp [h i hi] at hq

/-- The search succeeds (`firstIdx q n < n`) iff some index of the range is accepted. -/
theorem firstIdx_lt_iff : firstIdx q n < n ↔ ∃ i < n, q i = true := by
  unfold firstIdx
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => (Nat.find_spec h).1⟩
  · simp [h]

/-- The search is exhausted (`firstIdx q n = n`) iff every index of the range is rejected. -/
theorem firstIdx_eq_iff : firstIdx q n = n ↔ ∀ i < n, q i = false := by
  constructor
  · intro h i hi
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact absurd h (firstIdx_lt_iff.2 ⟨i, hi, hc⟩).ne
  · exact firstIdx_eq_of_forall

/-- A successful search returns an accepted index. -/
theorem q_firstIdx (h : firstIdx q n < n) : q (firstIdx q n) = true := by
  have h' := firstIdx_lt_iff.1 h
  unfold firstIdx
  rw [dif_pos h']
  exact (Nat.find_spec h').2

/-- Every index below the search index is rejected. -/
theorem firstIdx_min {i : ℕ} (hi : i < firstIdx q n) : q i = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have hlt : firstIdx q n < n := firstIdx_lt_iff.2 ⟨i, lt_of_lt_of_le hi firstIdx_le, hc⟩
  have h' := firstIdx_lt_iff.1 hlt
  unfold firstIdx at hi
  rw [dif_pos h'] at hi
  exact Nat.find_min h' hi ⟨lt_of_lt_of_le hi (Nat.find_spec h').1.le, hc⟩

/-- Two tests agreeing on the range have the same search index. -/
theorem firstIdx_congr {q' : ℕ → Bool} (h : ∀ i < n, q i = q' i) : firstIdx q n = firstIdx q' n := by
  unfold firstIdx
  have : (∃ i < n, q i = true) ↔ ∃ i < n, q' i = true :=
    ⟨fun ⟨i, hi, hq⟩ => ⟨i, hi, (h i hi) ▸ hq⟩, fun ⟨i, hi, hq⟩ => ⟨i, hi, (h i hi).symm ▸ hq⟩⟩
  by_cases hq : ∃ i < n, q i = true
  · rw [dif_pos hq, dif_pos (this.1 hq)]
    exact Nat.find_congr' fun {i} => and_congr_right fun hi => by rw [h i hi]
  · rw [dif_neg hq, dif_neg (fun h' => hq (this.2 h'))]

/-- **Bounded first-index search is polynomial-time:** if the test `p z i` is a polynomial-time
test of `⟨1^i, z⟩` and the bound `len z` is a unary function, then
`z ↦ 1^{firstIdx (p z) (len z)}` is polynomial-time computable.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` on the counter step
`cstep` from `⟨[], z⟩`, whose orbit is `⟨1^i, z⟩` (`cstep_iterate`) and polynomially bounded
for every word (`cstep_horbit`), with the acceptance test `len z ≤ i ∨ p z i`
(`Complexity.StateLoop.lenLe_comp`, `or_poly`), the payload `1^i` (the first projection), and
the round polynomial `C (n+1)^c` bounding `len` (`PolyTimeComputable.output_length_le`). The
loop's `List.find?` returns `firstIdx (p z) (len z)` by
`Complexity.StateLoop.find?_range_eq_some`: below it both disjuncts fail (`firstIdx_min`,
`firstIdx_le`), at it one holds (`q_firstIdx`, or `len z ≤ firstIdx` on exhaustion). -/
theorem polyTimeComputable_firstIdx {p : List Bool → ℕ → Bool}
    (hp : PolyTimeComputable fun w => [p (pairSndD w) (pairFstD w).length])
    {len : List Bool → ℕ} (hlen : PolyTimeComputable fun z => List.replicate (len z) true) :
    PolyTimeComputable fun z => List.replicate (firstIdx (p z) (len z)) true := by
  obtain ⟨C, c, hC⟩ := hlen.output_length_le
  have hlenP : ∀ z, len z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have hacc : PolyTimeComputable fun w =>
      [decide (len (pairSndD w) ≤ (pairFstD w).length) || p (pairSndD w) (pairFstD w).length] := by
    refine or_poly ?_ hp
    convert lenLe_comp polyTimeComputable_pairFstD (hlen.comp polyTimeComputable_pairSndD) using 1
    funext w
    simp
  have hF := polyTimeComputable_iterateFind cstep_poly hacc polyTimeComputable_pairFstD
    (PolyExpr.normal C c) (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hF.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : firstIdx (p z) (len z) ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length :=
    firstIdx_le.trans ((hlenP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega)))
  rw [find?_range_eq_some hN ?_ ?_]
  · show List.replicate (firstIdx (p z) (len z)) true =
      pairFstD (cstep^[firstIdx (p z) (len z)] (pairEncode [] z))
    rw [horb, pairFstD_pairEncode]
  · intro i hi
    rw [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    have h1 : ¬ len z ≤ i := by
      have := firstIdx_le (q := p z) (n := len z)
      omega
    simp [h1, firstIdx_min hi]
  · rw [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    by_cases h : firstIdx (p z) (len z) < len z
    · simp [q_firstIdx h]
    · simp [not_lt.1 h]

/-! ### The bit-extraction principle -/

/-- Emitting `f i` at the indices `i < L` of `List.range N` gives `(List.range (min N L)).map f`. -/
theorem flatMap_range_ite_eq (f : ℕ → Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then [f i] else []) =
      (List.range (min N L)).map f
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite_eq f L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.map_append, List.map_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- A list is the list of its bits read with default `false` (`List.ofFn_getElem`,
`List.getD_eq_getElem`). -/
theorem map_range_getD (l : List Bool) :
    (List.range l.length).map (fun i => l.getD i false) = l := by
  conv_rhs => rw [← List.ofFn_getElem l]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  simp [List.getD_eq_getElem?_getD]

/-- **The bit-extraction principle:** a string function `F` is polynomial-time computable as
soon as its length is a unary function and its `m`-th bit `(F z).getD m false` is a
polynomial-time test of `⟨1^m, z⟩`.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
`cstep` from `⟨[], z⟩` (orbit `⟨1^i, z⟩`, `cstep_iterate`; bound `cstep_horbit`) with the emitter
`⟨1^i, z⟩ ↦ if i < |F z| then [(F z).getD i false] else []` (`Complexity.polyTimeComputable_ite`
on `ltTest_poly` and the bit test) and the round polynomial `C (n+1)^c` bounding `|F z|`
(`PolyTimeComputable.output_length_le`). The emitted chunks concatenate to
`(List.range |F z|).map (fun i => (F z).getD i false) = F z` (`flatMap_range_ite_eq`,
`map_range_getD`). -/
theorem polyTimeComputable_of_getD {F : List Bool → List Bool}
    (hbit : PolyTimeComputable fun w => [(F (pairSndD w)).getD (pairFstD w).length false])
    (hlen : PolyTimeComputable fun z => List.replicate (F z).length true) :
    PolyTimeComputable F := by
  obtain ⟨C, c, hC⟩ := hlen.output_length_le
  have hlenP : ∀ z, (F z).length ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have hg : PolyTimeComputable fun w => List.replicate (F (pairSndD w)).length true :=
    hlen.comp polyTimeComputable_pairSndD
  have htest : PolyTimeComputable fun w =>
      [decide ((pairFstD w).length < (F (pairSndD w)).length)] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD) hg
  have hemit := polyTimeComputable_ite htest hbit (polyTimeComputable_const [])
  have hE := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hE.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : (F z).length ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hlenP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite_eq, min_eq_right hN, map_range_getD]

/-! ### Square roots in unary -/

/-- `Nat.sqrt` of a unary function is a unary function: the search for the least `i` with
`f x < (i + 1)²` over `i ≤ f x` (`polyTimeComputable_firstIdx`, `Nat.lt_succ_sqrt`,
`Nat.le_sqrt`). -/
theorem unarySqrt_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => List.replicate (Nat.sqrt (f x)) true := by
  have hi : PolyTimeComputable fun w => List.replicate ((pairFstD w).length + 1) true :=
    unaryAdd_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 1)
  have hp : PolyTimeComputable fun w =>
      [decide (f (pairSndD w) < ((pairFstD w).length + 1) * ((pairFstD w).length + 1))] :=
    ltTest_poly (hf.comp polyTimeComputable_pairSndD) (unaryMul_poly hi hi)
  have hlen : PolyTimeComputable fun z => List.replicate (f z + 1) true :=
    unaryAdd_poly hf (unaryConst_poly 1)
  convert polyTimeComputable_firstIdx (p := fun z i => decide (f z < (i + 1) * (i + 1))) hp hlen
    using 1
  funext z
  congr 1
  symm
  apply firstIdx_eq_of
  · exact Nat.lt_succ_of_le (Nat.sqrt_le_self _)
  · simpa using Nat.lt_succ_sqrt (f z)
  · intro i hi
    simpa using Nat.le_sqrt.1 hi

/-! ### Truncation -/

/-- Truncating a polynomial-time string to a unary length is polynomial-time
(`Complexity.polyTimeComputable_pairTakePoly` at the variable length). -/
theorem truncate_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {M : List Bool → ℕ} (hM : PolyTimeComputable fun x => List.replicate (M x) true) :
    PolyTimeComputable fun x => (s x).take (M x) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (hM.pairEncode hs) using 1
  funext x
  simp

/-! ### Counted loops -/

/-- **State loops** (a copy of the private `polyTimeComputable_stateFind` of
`TCSlib/Complexity/Randomized/Repetition.lean`, requested as a shared lemma). A state word
`⟨x, s⟩` retains the input `x` and evolves its state from `start x` by `s ↦ step ⟨x, s⟩`
(`Complexity.StateLoop.orbit`); a test `acc` on the state word is `false` before round `N x`
and `true` at round `N x ≤ R|x|`, the states up to that round have length at most `B|x|`, and
`out` reads the answer off the final state word. Then `x ↦ out ⟨x, orbit x (N x)⟩` is
polynomial-time computable.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` on the length-guarded
step `Complexity.StateLoop.gstep step B` with `R` as the round polynomial and
`StateLoop.gstepBound B` as the orbit bound (valid for every word by
`StateLoop.length_gstep_iterate_le`), pre-composed with `x ↦ ⟨x, start x⟩`. On the genuine
orbit the guard never fires (`StateLoop.gstep_iterate_eq`), so the loop's `find?` returns
`some (N x)` (`StateLoop.find?_range_eq_some`) and the payload is `out ⟨x, orbit x (N x)⟩`. -/
theorem polyTimeComputable_stateFind {start step : List Bool → List Bool}
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

/-- The state of a **counted loop** after `i` rounds: from `init x`, round `i` replaces the
state `s` by `upd ⟨x, ⟨1^i, s⟩⟩` (the update reads the input, the round counter and the state
off one word). -/
def loopState (upd init : List Bool → List Bool) (x : List Bool) : ℕ → List Bool
  | 0 => init x
  | i + 1 => upd (pairEncode x (pairEncode (List.replicate i true) (loopState upd init x i)))

/-- The initial state of a counted loop. -/
@[simp] theorem loopState_zero (upd init : List Bool → List Bool) (x : List Bool) :
    loopState upd init x 0 = init x := rfl

/-- One round of a counted loop. -/
@[simp] theorem loopState_succ (upd init : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    loopState upd init x (i + 1) =
      upd (pairEncode x (pairEncode (List.replicate i true) (loopState upd init x i))) := rfl

namespace CountLoop

/-- The initial state word `⟨[], init x⟩`: empty counter, initial state. -/
def start (init : List Bool → List Bool) (x : List Bool) : List Bool := pairEncode [] (init x)

/-- The step on `⟨x, ⟨cnt, s⟩⟩`: append a token to the counter and update the state. -/
def step (upd : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (true :: pairFstD (pairSndD w)) (upd w)

/-- The acceptance test on `⟨x, ⟨cnt, s⟩⟩`: the counter has reached `N x`. -/
def acc (N : List Bool → ℕ) (w : List Bool) : Bool :=
  decide (N (pairFstD w) ≤ (pairFstD (pairSndD w)).length)

/-- The output on `⟨x, ⟨cnt, s⟩⟩`: the state `s`. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The initial state word is polynomial-time. -/
theorem start_poly {init : List Bool → List Bool} (hinit : PolyTimeComputable init) :
    PolyTimeComputable (start init) :=
  (polyTimeComputable_const []).pairEncode hinit

/-- The step is polynomial-time. -/
theorem step_poly {upd : List Bool → List Bool} (hupd : PolyTimeComputable upd) :
    PolyTimeComputable (step upd) :=
  ((cons_poly true).comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    hupd

/-- The acceptance test is polynomial-time (`leTest_poly` against the unary round count). -/
theorem acc_poly {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true) :
    PolyTimeComputable fun w => [acc N w] := by
  have h1 : PolyTimeComputable fun w => List.replicate (N (pairFstD w)) true :=
    hN.comp polyTimeComputable_pairFstD
  exact leTest_poly h1
    (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The closed form of the orbit: `⟨1^i, loopState upd init x i⟩`. -/
theorem orbit_eq (upd init : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit (start init) (step upd) x i =
      pairEncode (List.replicate i true) (loopState upd init x i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [orbit_succ, ih]
    simp [step, List.replicate_succ]

end CountLoop

/-- **Counted loops are polynomial-time:** if the update and the initial state are
polynomial-time, the round count `N x` is a unary function, and the initial state and every
update of a state word `⟨x, s⟩` have length at most `B|x|`, then `x ↦ loopState upd init x (N x)`
is polynomial-time computable.

**Proof sketch.** A state loop (`polyTimeComputable_stateFind`, data in `CountLoop`) on the
state word `⟨x, ⟨1^i, S_i⟩⟩` with `S_i = loopState upd init x i` (`CountLoop.orbit_eq`): the step
appends a token to the counter and applies `upd` to the whole word; the acceptance test is the
length comparison `N x ≤ i` against `1^{N x}` (`leTest_poly`), `false` below round `N x` and
`true` there; the output projects the state. Every state has length at most `B|x|`
(`hinitB`, `hupdB`), so the orbit `⟨1^i, S_i⟩` has length at most `2 N x + 2 + B|x|`, and the
round polynomial `C (n+1)^c` bounding `N` comes from `PolyTimeComputable.output_length_le`. -/
theorem polyTimeComputable_loopState {upd init : List Bool → List Bool}
    (hupd : PolyTimeComputable upd) (hinit : PolyTimeComputable init)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true)
    (B : PolyExpr) (hinitB : ∀ x, (init x).length ≤ B.eval x.length)
    (hupdB : ∀ x s, (upd (pairEncode x s)).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => loopState upd init x (N x) := by
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNR : ∀ x, N x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hstate : ∀ x i, (loopState upd init x i).length ≤ B.eval x.length := by
    intro x i
    cases i with
    | zero => exact hinitB x
    | succ i => exact hupdB x _
  have hbound : ∀ x i, i ≤ N x →
      (orbit (CountLoop.start init) (CountLoop.step upd) x i).length ≤
        (PolyExpr.add (.mul (.const 2) (PolyExpr.normal C c)) (.add (.const 2) B)).eval
          x.length := by
    intro x i hi
    rw [CountLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have h1 := hstate x i
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

/-! ### Division and remainder in unary -/

/-- Euclidean division as a bounded search: `a / m` is the least `q` with `a < (q + 1) m`
(and `0` for `m = 0`). -/
noncomputable def divNum (a m : ℕ) : ℕ :=
  if m = 0 then 0 else firstIdx (fun q => decide (a < (q + 1) * m)) (a + 1)

/-- `divNum a m = a / m`. -/
theorem divNum_eq (a m : ℕ) : divNum a m = a / m := by
  unfold divNum
  split_ifs with h
  · simp [h]
  · have hm : 0 < m := Nat.pos_of_ne_zero h
    apply firstIdx_eq_of
    · exact Nat.lt_succ_of_le (Nat.div_le_self a m)
    · simp only [decide_eq_true_eq]
      rw [Nat.mul_comm]
      exact Nat.lt_mul_div_succ a hm
    · intro q hq
      simp only [decide_eq_false_iff_not, not_lt]
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hm] at hq
      exact hq

/-- The remainder `a - (a / m) m`. -/
noncomputable def modNum (a m : ℕ) : ℕ := a - divNum a m * m

/-- `modNum a m = a % m`. -/
theorem modNum_eq (a m : ℕ) : modNum a m = a % m := by
  unfold modNum
  rw [divNum_eq]
  exact (Nat.eq_sub_of_add_eq (Nat.mod_add_div' a m)).symm

/-- Division of unary functions is a unary function (`polyTimeComputable_firstIdx` with the
test `a < (q + 1) m`, `Complexity.polyTimeComputable_ite` for the zero divisor). -/
theorem divNum_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (divNum (f x) (g x)) true := by
  have hf' : PolyTimeComputable fun w => List.replicate (f (pairSndD w)) true :=
    hf.comp polyTimeComputable_pairSndD
  have hg' : PolyTimeComputable fun w => List.replicate (g (pairSndD w)) true :=
    hg.comp polyTimeComputable_pairSndD
  have hsearch : PolyTimeComputable fun x =>
      List.replicate (firstIdx (fun q => decide (f x < (q + 1) * g x)) (f x + 1)) true :=
    polyTimeComputable_firstIdx (p := fun x q => decide (f x < (q + 1) * g x))
      (ltTest_poly hf' (unaryMul_poly
        (unaryAdd_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 1)) hg'))
      (unaryAdd_poly hf (unaryConst_poly 1))
  unfold divNum
  convert polyTimeComputable_ite (eqTest_poly hg (unaryConst_poly 0)) (unaryConst_poly 0) hsearch
    using 1
  funext x
  by_cases h : g x = 0 <;> simp [h]

/-- The remainder of unary functions is a unary function. -/
theorem modNum_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (modNum (f x) (g x)) true :=
  unarySub_poly hf (unaryMul_poly (divNum_poly hf hg) hg)

/-! ### Binary length in unary -/

/-- `Nat.size` of a unary function is a unary function: the binary representation of the
length of `1^{f x}` (`Turing.FinTM.computesFunInTime_lengthBits`) has `Nat.size (f x)` digits
(`Nat.size_eq_bits_len`). -/
theorem unarySize_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => List.replicate (Nat.size (f x)) true := by
  have hbits : PolyTimeComputable fun x => Nat.bits x.length :=
    polyTimeComputable_of_linear Turing.FinTM.computesFunInTime_lengthBits
  convert unaryLength_poly (hbits.comp hf) using 1
  funext x
  simp [Nat.size_eq_bits_len]

end TCSlib.Cryptography.EncodingMachines
