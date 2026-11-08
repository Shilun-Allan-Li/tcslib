/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Iterate
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.CircuitComplexity.UnaryCode
import TCSlib.Complexity.ClassNP.PolyTimePrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counted loops, unary numbers and word tools in polynomial time

Generic polynomial-time word functions on `Turing.pairEncode`-structured inputs, shared by
the randomized algorithms of [AB09, §7.2.3–7.2.4]: a counted loop (a host: run a step once
per letter of a unary counter), the reading of unary numbers, the lookup of an entry in an
encoded list of words (`Complexity.BinArith.encWords`), word equality, unary multiplication,
and the cutting of a word into blocks. Not themselves results of the book.

## Main definitions

* `Complexity.BinArith.forLoop` — run a step once per letter of a unary counter.
* `Complexity.BinArith.uHead`, `Complexity.BinArith.uRest`, `Complexity.BinArith.hasFalse` —
  the leading `1`s of a word, the rest after the first `0`, and whether there is a `0`.
* `Complexity.BinArith.getW` — the `j`-th entry of an encoded list of words.
* `Complexity.BinArith.eqW` — equality of the two components of a pair.
* `Complexity.BinArith.mulU` — unary multiplication (`|a|` copies of `b` on `⟨a, b⟩`).
* `Complexity.BinArith.chunkW`, `Complexity.BinArith.chunkList` — cutting a word into blocks
  of `|c|` bits, as a list of words.

## Main results

* `Complexity.BinArith.forLoop_pairEncode`, `Complexity.BinArith.polyTimeComputable_forLoop`,
  `Complexity.BinArith.forLoop_bound_of_ctx` — the counted loop and its time bound.
* `Complexity.BinArith.decodeNat_eq` — `BoolCircuit.decodeNat` through `uHead` and `uRest`.
* `Complexity.BinArith.getW_pairEncode`, `Complexity.BinArith.polyTimeComputable_getW`.
* `Complexity.BinArith.eqW_pairEncode`, `Complexity.BinArith.length_mulU`,
  `Complexity.BinArith.chunkW_pairEncode` — what they compute, and their
  `polyTimeComputable_*` lemmas.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Complexity

namespace BinArith

open Turing
open Complexity.LogProg (bitsVal eq_of_bitsVal_eq)

/-- Composition in applied form: `x ↦ f (g x)` is polynomial-time when `f` and `g` are.  (Stated
with an applied body so that unification never unfolds `f`.) -/
theorem polyTimeComputable_app {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable (fun x => f (g x)) :=
  hf.comp hg

/-- A one-bit test of a polynomial-time function, in applied form. -/
theorem polyTimeComputable_test_app {p : List Bool → Bool} {g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => [p (g x)]) :=
  hp.comp hg

/-! ### The counted loop -/

/-- One round of the counted loop on `⟨c, d⟩`: if `c ≠ []`, drop a letter of `c` and apply
`f` to `d`; a state with empty (or malformed) counter is fixed. -/
def forStep (f : List Bool → List Bool) (S : List Bool) : List Bool :=
  if isNilB (pairFstD S) then S else pairEncode ((pairFstD S).drop 1) (f (pairSndD S))

/-- The counted loop: `|S| + 1` rounds of `forStep f` from `S`. -/
def forLoop (f : List Bool → List Bool) (S : List Bool) : List Bool :=
  (forStep f)^[1 * (S.length + 1) ^ 1] S

/-- The rounds of the counted loop from `⟨c, d⟩`. -/
theorem iterate_forStep (f : List Bool → List Bool) (c d : List Bool) (i : ℕ) :
    (forStep f)^[i] (pairEncode c d) = pairEncode (c.drop i) (f^[min i c.length] d) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : c.length ≤ i
    · have h1 : min i c.length = c.length := by omega
      have h2 : min (i + 1) c.length = c.length := by omega
      simp [forStep, isNilB, List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega :
        c.length ≤ i + 1), h1, h2]
    · have hne : c.drop i ≠ [] := by simp; omega
      have h1 : min i c.length = i := by omega
      have h2 : min (i + 1) c.length = i + 1 := by omega
      simp only [forStep, pairFstD_pairEncode, pairSndD_pairEncode, isNilB, hne,
        decide_false, Bool.false_eq_true, if_false, List.drop_drop, h1, h2,
        Function.iterate_succ_apply']

/-- **The counted loop runs `f` once per letter of the counter**:
`forLoop f ⟨c, d⟩ = ⟨[], f^[|c|] d⟩`. -/
theorem forLoop_pairEncode (f : List Bool → List Bool) (c d : List Bool) :
    forLoop f (pairEncode c d) = pairEncode [] (f^[c.length] d) := by
  unfold forLoop
  rw [iterate_forStep, List.drop_eq_nil_of_le (by simp [length_pairEncode]; omega)]
  congr 2
  simp [length_pairEncode]
  omega

/-- A state whose counter is empty is fixed by the round. -/
theorem forStep_of_fst_nil (f : List Bool → List Bool) {S : List Bool} (h : pairFstD S = []) :
    forStep f S = S := by
  simp [forStep, isNilB, h]

/-- **The counted loop is polynomial-time** when its body is and the iterates `f^[j] d`,
`j ≤ |c|`, stay inside a polynomial envelope of `|⟨c, d⟩|`.

**Proof sketch.** `forLoop f` is `polyTimeComputable_iterate` of the round `forStep f` (an
`ite` of polynomial-time pieces) from the input. A word that is not a pair has empty counter
and is fixed; on `⟨c, d⟩` the `i`-th iterate is `⟨c.drop i, f^[min i |c|] d⟩`
(`iterate_forStep`), whose length the envelope bounds. -/
theorem polyTimeComputable_forLoop {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (B b : ℕ) (hbound : ∀ c d j, j ≤ c.length →
      (f^[j] d).length ≤ B * ((pairEncode c d).length + 1) ^ b) :
    PolyTimeComputable (forLoop f) := by
  have hstep : PolyTimeComputable (forStep f) := by
    unfold forStep
    exact polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      polyTimeComputable_id
      ((polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
        (hf.comp polyTimeComputable_pairSndD))
  refine polyTimeComputable_iterate hstep polyTimeComputable_id 1 1 (B + 2) (b + 1)
    (fun S i _ => ?_)
  simp only [id]
  have hP : 1 ≤ (S.length + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have hpow : (S.length + 1) ^ (b + 1) = (S.length + 1) ^ b * (S.length + 1) := pow_succ _ _
  have h5 : S.length + 1 ≤ (S.length + 1) ^ b * (S.length + 1) := Nat.le_mul_of_pos_left _ hP
  rw [hpow]
  cases hd : pairDecode S with
  | none =>
    have h0 : pairFstD S = [] := by simp [pairFstD, hd]
    rw [Function.iterate_fixed (forStep_of_fst_nil f h0)]
    nlinarith
  | some cd =>
    obtain ⟨c, d⟩ := cd
    have hS := eq_pairEncode_of_pairDecode S c d hd
    have h1 := hbound c d (min i c.length) (by omega)
    rw [← hS] at h1
    rw [hS, iterate_forStep, length_pairEncode]
    rw [← hS]
    have h2 : (c.drop i).length ≤ c.length := by simp
    have h3 : 2 * c.length + 2 ≤ S.length := by rw [hS]; simp [length_pairEncode]
    have h6 : B * (S.length + 1) ^ b ≤ B * ((S.length + 1) ^ b * (S.length + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    nlinarith

/-- An iterate bound for context-preserving bodies: if `f ⟨q, ·⟩` keeps `q` and grows the
word by at most `A(|q| + 1)`, then `|f^[j] d| ≤ |d| + jA(|q| + 1)`. -/
theorem length_iterate_le_of_ctx {f : List Bool → List Bool} (A : ℕ)
    (hctx : ∀ d, pairFstD (f d) = pairFstD d)
    (hlen : ∀ d, (f d).length ≤ d.length + A * ((pairFstD d).length + 1)) (d : List Bool) (j : ℕ) :
    (f^[j] d).length ≤ d.length + j * (A * ((pairFstD d).length + 1)) := by
  have hq : ∀ j, pairFstD (f^[j] d) = pairFstD d := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hctx, ih]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have := hlen (f^[j] d)
    rw [hq j] at this
    rw [Nat.succ_mul]
    omega

/-- The envelope required by `polyTimeComputable_forLoop`, for context-preserving bodies of
bounded growth. -/
theorem forLoop_bound_of_ctx {f : List Bool → List Bool} (A : ℕ)
    (hctx : ∀ d, pairFstD (f d) = pairFstD d)
    (hlen : ∀ d, (f d).length ≤ d.length + A * ((pairFstD d).length + 1)) :
    ∀ c d j, j ≤ c.length → (f^[j] d).length ≤ (A + 1) * ((pairEncode c d).length + 1) ^ 2 := by
  intro c d j hj
  have h := length_iterate_le_of_ctx A hctx hlen d j
  have hq := length_pairFstD_le d
  have hN : c.length + d.length ≤ (pairEncode c d).length := by simp [length_pairEncode]; omega
  set N := (pairEncode c d).length
  have h1 : j * (A * ((pairFstD d).length + 1)) ≤ N * (A * (N + 1)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  nlinarith

/-! ### Unary numbers -/

/-- The transition of `uHead`: stay live while reading `1`s. -/
private def headδ (q b : Bool) : Bool := q && b

/-- The emission of `uHead`: copy the `1`s of the live phase. -/
private def headO (q b : Bool) : Option Bool := if q && b then some true else none

/-- The leading `1`s of a word (`1ʲ` on `1ʲ0w`). -/
def uHead (w : List Bool) : List Bool := transduce headδ headO true w

/-- The transition of `uRest`: switch on at the first `0`. -/
private def restδ (q b : Bool) : Bool := q || !b

/-- The emission of `uRest`: copy everything after the first `0`. -/
private def restO (q b : Bool) : Option Bool := if q then some b else none

/-- The word after the first `0` (`w` on `1ʲ0w`; `[]` if there is no `0`). -/
def uRest (w : List Bool) : List Bool := transduce restδ restO false w

/-- Whether a word contains a `0`. -/
def hasFalse (w : List Bool) : Bool := (w.map not).any id

/-- The `uHead` transducer emits nothing once off. -/
private theorem transduce_head_false (w : List Bool) : transduce headδ headO false w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [transduce, headδ, headO, ih]

/-- The `uRest` transducer copies everything once on. -/
private theorem transduce_rest_true (w : List Bool) : transduce restδ restO true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [transduce, restδ, restO, ih]

/-- `uHead` on `0w` is empty. -/
@[simp] theorem uHead_false_cons (w : List Bool) : uHead (false :: w) = [] := by
  simp [uHead, transduce, headδ, headO, transduce_head_false]

/-- `uHead` on `1w`. -/
@[simp] theorem uHead_true_cons (w : List Bool) : uHead (true :: w) = true :: uHead w := by
  simp [uHead, transduce, headδ, headO]

/-- `uRest` on `0w` is `w`. -/
@[simp] theorem uRest_false_cons (w : List Bool) : uRest (false :: w) = w := by
  simp [uRest, transduce, restδ, restO, transduce_rest_true]

/-- `uRest` on `1w`. -/
@[simp] theorem uRest_true_cons (w : List Bool) : uRest (true :: w) = uRest w := by
  simp [uRest, transduce, restδ, restO]

/-- `uHead []` is empty. -/
@[simp] theorem uHead_nil : uHead [] = [] := rfl

/-- `uRest []` is empty. -/
@[simp] theorem uRest_nil : uRest [] = [] := rfl

/-- `hasFalse` on a cons. -/
@[simp] theorem hasFalse_cons (b : Bool) (w : List Bool) :
    hasFalse (b :: w) = (!b || hasFalse w) := by
  simp [hasFalse]

/-- `[]` has no `0`. -/
@[simp] theorem hasFalse_nil : hasFalse [] = false := rfl

/-- **Reading a unary number**: `decodeNat w` is `(|uHead w|, uRest w)` if `w` has a `0`. -/
theorem decodeNat_eq (w : List Bool) :
    BoolCircuit.decodeNat w =
      if hasFalse w then some ((uHead w).length, uRest w) else none := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp [BoolCircuit.decodeNat]
    · simp only [BoolCircuit.decodeNat, ih, uHead_true_cons, uRest_true_cons, hasFalse_cons,
        Bool.not_true, Bool.false_or, List.length_cons]
      split <;> simp

/-- Reading `1ʲ0w`. -/
theorem uHead_encodeNat (j : ℕ) (w : List Bool) :
    uHead (BoolCircuit.encodeNat j ++ w) = List.replicate j true := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat]
  | succ j ih => simpa [BoolCircuit.encodeNat, List.replicate_succ] using ih

/-- The rest of `1ʲ0w` is `w`. -/
theorem uRest_encodeNat (j : ℕ) (w : List Bool) :
    uRest (BoolCircuit.encodeNat j ++ w) = w := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat]
  | succ j ih => simpa [BoolCircuit.encodeNat, List.replicate_succ] using ih

/-- `1ʲ0w` has a `0`. -/
theorem hasFalse_encodeNat (j : ℕ) (w : List Bool) :
    hasFalse (BoolCircuit.encodeNat j ++ w) = true := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat]
  | succ j ih => simpa [BoolCircuit.encodeNat, List.replicate_succ] using ih

/-- A word with a `0` is `1ʲ0w` for `1ʲ = uHead`, `w = uRest`. -/
theorem eq_encodeNat_of_hasFalse {w : List Bool} (h : hasFalse w = true) :
    w = BoolCircuit.encodeNat (uHead w).length ++ uRest w := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    cases b
    · simp [BoolCircuit.encodeNat]
    · simp only [hasFalse_cons, Bool.not_true, Bool.false_or] at h
      have := ih h
      simp only [uHead_true_cons, uRest_true_cons, List.length_cons, BoolCircuit.encodeNat,
        List.replicate_succ, List.cons_append] at this ⊢
      exact congrArg _ this

/-- `uRest w` is no longer than `w`. -/
theorem length_uRest_le (w : List Bool) : (uRest w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp
    · simp only [uRest_true_cons, List.length_cons]; omega

/-- `uHead w` is no longer than `w`. -/
theorem length_uHead_le (w : List Bool) : (uHead w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp
    · simp only [uHead_true_cons, List.length_cons]; omega

/-- `uHead` is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_uHead : PolyTimeComputable uHead :=
  polyTimeComputable_transduce headδ headO true

/-- `uRest` is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_uRest : PolyTimeComputable uRest :=
  polyTimeComputable_transduce restδ restO false

/-- `hasFalse` is polynomial-time (negate, then test for a `1`). -/
theorem polyTimeComputable_hasFalse : PolyTimeComputable (fun w => [hasFalse w]) := by
  have hneg : PolyTimeComputable (transduce (σ := Unit) (fun _ _ => ()) (fun _ b => some !b) ()) :=
    polyTimeComputable_transduce _ _ ()
  have heq : ∀ w : List Bool,
      transduce (σ := Unit) (fun _ _ => ()) (fun _ b => some !b) () w = w.map not := by
    intro w
    induction w with
    | nil => rfl
    | cons b w ih => simp [transduce, ih]
  convert polyTimeComputable_any.comp hneg using 1
  funext w
  simp [hasFalse, heq]

/-! ### Lookup in a list of words -/

/-- The entry of index `|J|` of the list encoded in `L`, on `⟨J, L⟩` (`[]` past the end). -/
def getW (z : List Bool) : List Bool := pairFstD (pairSndD (forLoop pairSndD z))

/-- Peeling `j` entries of an encoded list. -/
theorem iterate_pairSndD_encWords (L : List (List Bool)) (j : ℕ) :
    pairSndD^[j] (encWords L) = encWords (L.drop j) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases L with
    | nil => exact iterate_pairSndD_nil j
    | cons w L => simp [ih]

/-- **Lookup**: `getW ⟨J, [w₀, …]⟩ = w_{|J|}` (`[]` past the end). -/
theorem getW_pairEncode (J : List Bool) (L : List (List Bool)) :
    getW (pairEncode J (encWords L)) = L.getD J.length [] := by
  rw [getW, forLoop_pairEncode, pairSndD_pairEncode, iterate_pairSndD_encWords,
    List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases L.drop J.length with
  | nil => rfl
  | cons w L' => simp

/-- Lookup in a list of binary numbers: the value of the entry, `0` past the end. -/
theorem getW_pairEncode_bits (J : List Bool) (vs : List ℕ) :
    getW (pairEncode J (encWords (vs.map Nat.bits))) = Nat.bits (vs.getD J.length 0) := by
  rw [getW_pairEncode]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[J.length]? <;> simp [Nat.zero_bits]

/-- Lookup is polynomial-time. -/
theorem polyTimeComputable_getW : PolyTimeComputable getW := by
  have hl : PolyTimeComputable (forLoop pairSndD) := by
    refine polyTimeComputable_forLoop polyTimeComputable_pairSndD 1 1 (fun c d j _ => ?_)
    have := length_iterate_pairSndD_le d j
    simp [length_pairEncode]
    omega
  exact polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hl)

/-! ### Equality, unary multiplication and cutting into blocks -/

/-- Either both projections are empty or the word is the pair of its projections. -/
private theorem pair_cases (z : List Bool) :
    (pairFstD z = [] ∧ pairSndD z = []) ∨ z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => left; simp [pairFstD, pairSndD, hd]
  | some ab =>
    right
    obtain ⟨a, b⟩ := ab
    simpa [pairFstD, pairSndD, hd] using eq_pairEncode_of_pairDecode z a b hd

/-- Word equality on `⟨a, b⟩`: equal lengths and equal values. -/
def eqW (z : List Bool) : Bool :=
  decide ((pairFstD z).length = (pairSndD z).length) && beq z

/-- `eqW ⟨a, b⟩` decides `a = b`. -/
theorem eqW_pairEncode (a b : List Bool) : eqW (pairEncode a b) = decide (a = b) := by
  simp only [eqW, beq, pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra hc
    push_neg at hc
    exact h (eq_of_bitsVal_eq hc.1 hc.2)

/-- Word equality is polynomial-time. -/
theorem polyTimeComputable_eqW : PolyTimeComputable (fun z => [eqW z]) :=
  polyTimeComputable_and polyTimeComputable_lenEq polyTimeComputable_beq

/-- One round of unary multiplication on `⟨b, acc⟩`: append `b` to `acc`. -/
private def mulUStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d) (pairSndD d ++ pairFstD d)

/-- Unary multiplication: on `⟨a, b⟩`, `|a|` copies of `b`. -/
def mulU (z : List Bool) : List Bool :=
  pairSndD (pairSndD (forLoop mulUStep (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))

/-- The rounds of unary multiplication. -/
private theorem iterate_mulUStep (b acc : List Bool) (j : ℕ) :
    mulUStep^[j] (pairEncode b acc) = pairEncode b (acc ++ (List.replicate j b).flatten) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [mulUStep, List.replicate_succ', List.flatten_append]

/-- `|mulU ⟨a, b⟩| = |a| · |b|`. -/
theorem length_mulU (a b : List Bool) : (mulU (pairEncode a b)).length = a.length * b.length := by
  simp [mulU, forLoop_pairEncode, iterate_mulUStep, List.length_flatten, List.sum_replicate]

/-- Unary multiplication is polynomial-time. -/
theorem polyTimeComputable_mulU : PolyTimeComputable mulU := by
  have hs : PolyTimeComputable mulUStep :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairSndD.append
      polyTimeComputable_pairFstD)
  have hl := polyTimeComputable_forLoop hs 3 2 (forLoop_bound_of_ctx 2
    (fun d => by simp [mulUStep]) (fun d => by
      rcases pair_cases d with ⟨h1, h2⟩ | h
      · simp [mulUStep, h1, h2, length_pairEncode]
      · obtain ⟨a, b, rfl⟩ : ∃ a b, d = pairEncode a b := ⟨_, _, h⟩
        simp [mulUStep, length_pairEncode]; omega))
  exact polyTimeComputable_slot3.comp (hl.comp (polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))))

/-- One round of cutting on `⟨c, ⟨rest, acc⟩⟩`: move the first `|c|` bits of `rest` to a new
entry of the word list `acc`; fixed once `rest` is empty. -/
private def chunkStep (d : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD d)) then d
  else pairEncode (pairFstD d)
    (pairEncode (PrefixByLength.drop (pairEncode (pairFstD d) (pairFstD (pairSndD d))))
      (pairSndD (pairSndD d) ++
        pairEncode (PrefixByLength.take (pairEncode (pairFstD d) (pairFstD (pairSndD d)))) []))

/-- Cutting `w` into blocks of `|c|` bits, on `⟨c, w⟩`; the result is a word list. -/
def chunkW (z : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (forLoop chunkStep
    (pairEncode (pairSndD z) (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))))

/-- The first `N` blocks of `c` bits of `w`. -/
def chunkList (c : ℕ) (w : List Bool) (N : ℕ) : List (List Bool) :=
  (List.range N).map fun i => (w.drop (i * c)).take c

/-- A round of cutting on a genuine state. -/
private theorem chunkStep_pairEncode (c rest acc : List Bool) :
    chunkStep (pairEncode c (pairEncode rest acc)) = if rest = [] then
      pairEncode c (pairEncode rest acc) else pairEncode c (pairEncode (rest.drop c.length)
        (acc ++ pairEncode (rest.take c.length) [])) := by
  simp [chunkStep, isNilB, PrefixByLength.take, PrefixByLength.drop]

/-- `N` rounds of cutting a word of `N` blocks. -/
private theorem iterate_chunkStep (c : List Bool) :
    ∀ (N : ℕ) (w : List Bool) (L : List (List Bool)), w.length = N * c.length →
      (0 < c.length ∨ N = 0) → chunkStep^[N] (pairEncode c (pairEncode w (encWords L))) =
        pairEncode c (pairEncode [] (encWords (L ++ chunkList c.length w N)))
  | 0, w, L, h, _ => by simp_all [chunkList]
  | N + 1, w, L, h, hc => by
    have hc' : 0 < c.length := by omega
    have hw : w ≠ [] := by rintro rfl; simp at h; simp [h] at hc'
    rw [Function.iterate_succ_apply, chunkStep_pairEncode, if_neg hw,
      ← encWords_append_singleton,
      iterate_chunkStep c N _ _ (by simp [h, Nat.succ_mul]) (Or.inl hc')]
    congr 3
    simp only [chunkList, List.range_succ_eq_map, List.map_cons, List.map_map, zero_mul,
      List.drop_zero, List.append_assoc, List.singleton_append]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- **Cutting into blocks**: if `|w| = N·|c|` then `chunkW ⟨c, w⟩` lists the `N` blocks. -/
theorem chunkW_pairEncode (c w : List Bool) (N : ℕ) (h : w.length = N * c.length)
    (hc : 0 < c.length ∨ N = 0) :
    chunkW (pairEncode c w) = encWords (chunkList c.length w N) := by
  have hN : N ≤ w.length := by
    rcases hc with hc | rfl
    · rw [h]; exact Nat.le_mul_of_pos_right _ hc
    · exact Nat.zero_le _
  have he := iterate_chunkStep c N w [] h hc
  simp only [encWords, List.flatMap_nil, List.nil_append] at he
  simp only [chunkW, pairFstD_pairEncode, pairSndD_pairEncode, forLoop_pairEncode]
  rw [show w.length = (w.length - N) + N by omega, Function.iterate_add_apply, he,
    Function.iterate_fixed (by rw [chunkStep_pairEncode, if_pos rfl])]
  simp [encWords]

/-- Cutting is polynomial-time.

**Proof sketch.** The round is assembled from the projections, the prefix operations and
`polyTimeComputable_ite`; it keeps `c` and grows a genuine state by `2` bits (the moved bits
are re-encoded once), so `forLoop_bound_of_ctx` bounds the counted loop. -/
theorem polyTimeComputable_chunkW : PolyTimeComputable chunkW := by
  have hcr := polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2
  have hs : PolyTimeComputable chunkStep := by
    unfold chunkStep
    exact polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_slot2)
      polyTimeComputable_id (polyTimeComputable_pairFstD.pairEncode
        ((polyTimeComputable_dropPrefixByLength.comp hcr).pairEncode
          (polyTimeComputable_slot3.append
            ((polyTimeComputable_takePrefixByLength.comp hcr).pairEncode
              (polyTimeComputable_const [])))))
  have hctx : ∀ d, pairFstD (chunkStep d) = pairFstD d := fun d => by
    unfold chunkStep; split_ifs <;> simp
  have hlen : ∀ d, (chunkStep d).length ≤ d.length + 2 * ((pairFstD d).length + 1) := by
    intro d
    by_cases hr : pairFstD (pairSndD d) = []
    · simp [chunkStep, isNilB, hr]
    rcases pair_cases d with ⟨-, h2⟩ | h
    · simp [h2, pairFstD, pairDecode] at hr
    obtain ⟨c, S, rfl⟩ : ∃ c S, d = pairEncode c S := ⟨_, _, h⟩
    simp only [pairSndD_pairEncode] at hr
    rcases pair_cases S with ⟨h1, -⟩ | hS
    · exact absurd h1 hr
    obtain ⟨rest, acc, rfl⟩ : ∃ a b, S = pairEncode a b := ⟨_, _, hS⟩
    simp only [pairFstD_pairEncode] at hr
    rw [chunkStep_pairEncode, if_neg hr]
    simp only [length_pairEncode, List.length_append, List.length_drop, List.length_take,
      List.length_nil, pairFstD_pairEncode]
    omega
  have hl := polyTimeComputable_forLoop hs 3 2 (forLoop_bound_of_ctx 2 hctx hlen)
  exact (polyTimeComputable_pairSndD.comp polyTimeComputable_slot3).comp
    (hl.comp (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])))))

end BinArith

end Complexity
