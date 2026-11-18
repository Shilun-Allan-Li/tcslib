/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.SeedMajority.Words
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.ClassNP.PolyTimePrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The counting state of the seed-majority host

Each state retains the original input and two binary counters. The total
step reads one padded seed word, increments the rank, and increments the
acceptance count by the test bit. The outer iteration keeps its length guard,
so no fixed state bound is claimed after termination.

## Main definitions

* `Complexity.SeedMajority.seedFor`: the seed read from a raw counting state.
* `Complexity.SeedMajority.advance`: one counting round.
* `Complexity.SeedMajority.finished`: the terminal-rank test.
* `Complexity.SeedMajority.payload`: the strict-majority bit.

## Main results

* The four maps are polynomial-time when the test is in `P` and the width
  has an FP unary word.
* `Complexity.SeedMajority.length_state_le`: the counters fit in `w+1` bits
  up to and including the terminal rank.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §7.1, p. 126.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1, step 4.
-/

namespace Complexity.SeedMajority

open Turing

/-- The seed extracted from `z` is the first `w |fst z|` letters of its raw
rank word followed by the binary power-of-two padding. On counting states,
`seedFor w (state x i a) = word (w |x|) i`. [AB09, §7.1, p. 126] -/
def seedFor (w : ℕ → ℕ) (z : List Bool) : List Bool :=
  (pairFstD (pairSndD z) ++ Nat.bits (2 ^ w (pairFstD z).length)).take
    (w (pairFstD z).length)

/-- The raw-state seed reader satisfies
`seedFor w z = (fst(snd z) ++ bits(2^(w |fst z|))).take (w |fst z|)`. -/
theorem seedFor_eq (w : ℕ → ℕ) (z : List Bool) :
    seedFor w z =
      (pairFstD (pairSndD z) ++ Nat.bits (2 ^ w (pairFstD z).length)).take
        (w (pairFstD z).length) := rfl

/-- On a counting state the extracted seed is its width-`w |x|` rank word:
`seedFor w (state x i a) = word (w |x|) i`. -/
theorem seedFor_state (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
    seedFor w (state x i a) = word (w x.length) i := by
  simp only [seedFor_eq, state_eq, pairFstD_pairEncode, pairSndD_pairEncode, word_eq]

/-- Binary exponential fuel is FP when the width has an FP unary word:
`x ↦ bits(2^(w |x|))` is FP. This reuses the shared power-of-two evaluator.
[PS10, Theorem 180.1, final paragraph of the proof] -/
theorem polyTimeComputable_seedFuel {w : ℕ → ℕ}
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    PolyTimeComputable fun x => Nat.bits (2 ^ w x.length) := by
  convert BinArith.polyTimeComputable_powerOfTwo.comp hw using 1
  funext x
  simp only [Function.comp_apply, List.length_replicate]

/-- Reading the rank seed is FP:
`PolyTimeComputable (seedFor w)` when the unary width is FP.

**Proof sketch.** Compose the unary width and binary fuel evaluators with
the first projection. Append the raw rank to the padding word and apply
the existing prefix-by-length machine to the pair of unary width and data. -/
theorem polyTimeComputable_seedFor {w : ℕ → ℕ}
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    PolyTimeComputable (seedFor w) := by
  have hwidth := hw.comp polyTimeComputable_pairFstD
  have hpad := (polyTimeComputable_seedFuel hw).comp polyTimeComputable_pairFstD
  have hrank := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hdata := hrank.append hpad
  convert polyTimeComputable_takePrefixByLength.comp (hwidth.pairEncode hdata) using 1
  funext z
  simp only [Function.comp_apply, seedFor_eq, PrefixByLength.take_def,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- One total counting round keeps the input and increments the binary counters:
`advance V w (state x i a) = state x (i+1) (a + [⟨x,word (w |x|) i⟩ ∈ V])`.
The step is total; the outer host retains its size guard after termination.
[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, final paragraph of the proof] -/
noncomputable def advance (V : Language Bool) (w : ℕ → ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z)
    (pairEncode (BinArith.add (pairEncode (pairFstD (pairSndD z)) (Nat.bits 1)))
      (BinArith.add (pairEncode (pairSndD (pairSndD z))
        (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (seedFor w z))
          then Nat.bits 1 else Nat.bits 0))))

/-- The counting-round reader exposes the binary additions and indicator:
`advance V w z = ⟨fst z, ⟨add(⟨fst(snd z),bits 1⟩),
add(⟨snd(snd z), if indicator V ⟨fst z,seedFor w z⟩ then bits 1 else bits 0⟩)⟩⟩`. -/
theorem advance_eq (V : Language Bool) (w : ℕ → ℕ) (z : List Bool) :
    advance V w z = pairEncode (pairFstD z)
      (pairEncode (BinArith.add (pairEncode (pairFstD (pairSndD z)) (Nat.bits 1)))
        (BinArith.add (pairEncode (pairSndD (pairSndD z))
          (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (seedFor w z))
            then Nat.bits 1 else Nat.bits 0)))) := rfl

/-- Each counting round is FP for `V ∈ P` and an FP unary width:
`PolyTimeComputable (advance V w)`.

**Proof sketch.** Read the input and counters with total pair projections.
The seed is `polyTimeComputable_seedFor`; apply the `P` indicator to its
pair with the input. Its Boolean result selects the constant increment
zero or one. Pairing and the published binary adder assemble the next state.
This proof establishes FP for every raw word, including malformed states. -/
theorem polyTimeComputable_advance {V : Language Bool} (hV : V ∈ P) {w : ℕ → ℕ}
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    PolyTimeComputable (advance V w) := by
  have hrank := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hcount := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have htest := (mem_P_iff_polyTimeComputable.mp hV).comp
    (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_seedFor hw))
  have hbit := polyTimeComputable_ite htest
    (polyTimeComputable_const (Nat.bits 1)) (polyTimeComputable_const (Nat.bits 0))
  have hi := BinArith.polyTimeComputable_add.comp
    (hrank.pairEncode (polyTimeComputable_const (Nat.bits 1)))
  have ha := BinArith.polyTimeComputable_add.comp (hcount.pairEncode hbit)
  convert polyTimeComputable_pairFstD.pairEncode (hi.pairEncode ha) using 1

open Classical in
/-- On a counting state one round has its intended arithmetic meaning:
`advance V w (state x i a) = state x (i+1) (a + [⟨x,word(w |x|) i⟩ ∈ V])`.
[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, final paragraph of the proof] -/
theorem advance_state (V : Language Bool) (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
    advance V w (state x i a) = state x (i + 1)
      (a + if pairEncode x (word (w x.length) i) ∈ V then 1 else 0) := by
  rw [advance_eq, seedFor_state]
  simp only [state_eq, pairFstD_pairEncode, pairSndD_pairEncode, BinArith.add_pairEncode,
    MultiTapeTM.indicator_def]
  by_cases h : pairEncode x (word (w x.length) i) ∈ V
  · simp only [if_pos h, ↓reduceIte, BinArith.add_pairEncode]
  · simp only [if_neg h, Bool.false_eq_true, ↓reduceIte, BinArith.add_pairEncode, Nat.add_zero]

/-- The terminal test compares the rank with its binary fuel:
`finished w z = beq ⟨fst(snd z), bits(2^(w |fst z|))⟩`.
[PS10, Theorem 180.1, final paragraph of the proof] -/
def finished (w : ℕ → ℕ) (z : List Bool) : Bool :=
  BinArith.beq (pairEncode (pairFstD (pairSndD z)) (Nat.bits (2 ^ w (pairFstD z).length)))

/-- The terminal test satisfies
`finished w z = beq ⟨fst(snd z),bits(2^(w |fst z|))⟩`. -/
theorem finished_eq (w : ℕ → ℕ) (z : List Bool) :
    finished w z = BinArith.beq
      (pairEncode (pairFstD (pairSndD z)) (Nat.bits (2 ^ w (pairFstD z).length))) := rfl

/-- The terminal test is FP:
`z ↦ [finished w z]` is FP when the unary width is FP. -/
theorem polyTimeComputable_finished {w : ℕ → ℕ}
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    PolyTimeComputable fun z => [finished w z] := by
  have hrank := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hpower := (polyTimeComputable_seedFuel hw).comp polyTimeComputable_pairFstD
  convert BinArith.polyTimeComputable_beq.comp (hrank.pairEncode hpower) using 1

/-- A counting state is terminal exactly at the fuel rank:
`finished w (state x i a) = decide (i = 2^(w |x|))`. -/
theorem finished_state (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
    finished w (state x i a) = decide (i = 2 ^ w x.length) := by
  simp only [finished_eq, state_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.beq_pairEncode]

/-- The output bit tests whether the doubled count exceeds the fuel:
`payload w z = [lt ⟨bits(2^(w |fst z|)),add ⟨snd(snd z),snd(snd z)⟩⟩]`.
[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, final paragraph of the proof] -/
def payload (w : ℕ → ℕ) (z : List Bool) : List Bool :=
  [BinArith.lt (pairEncode (Nat.bits (2 ^ w (pairFstD z).length))
    (BinArith.add (pairEncode (pairSndD (pairSndD z)) (pairSndD (pairSndD z)))))]

/-- The output reader satisfies
`payload w z = [lt ⟨bits(2^(w |fst z|)),add ⟨snd(snd z),snd(snd z)⟩⟩]`. -/
theorem payload_eq (w : ℕ → ℕ) (z : List Bool) :
    payload w z = [BinArith.lt (pairEncode (Nat.bits (2 ^ w (pairFstD z).length))
      (BinArith.add (pairEncode (pairSndD (pairSndD z)) (pairSndD (pairSndD z)))))] := rfl

/-- The payload is FP: `PolyTimeComputable (payload w)` for an FP unary width.
It composes binary doubling by addition with the shared strict comparator. -/
theorem polyTimeComputable_payload {w : ℕ → ℕ}
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    PolyTimeComputable (payload w) := by
  have hcount := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hdouble := BinArith.polyTimeComputable_add.comp (hcount.pairEncode hcount)
  have hpower := (polyTimeComputable_seedFuel hw).comp polyTimeComputable_pairFstD
  convert BinArith.polyTimeComputable_lt.comp (hpower.pairEncode hdouble) using 1

/-- On a counting state, the payload is the strict majority test:
`payload w (state x i a) = [decide (2^(w |x|) < 2*a)]`.
Equality of the two sides of the comparison rejects. -/
theorem payload_state (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
    payload w (state x i a) = [decide (2 ^ w x.length < 2 * a)] := by
  simp only [payload_eq, state_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.add_pairEncode, BinArith.lt_pairEncode, two_mul]

/-- The initial state `x ↦ state x 0 0` is FP, by pairing with two constant words. -/
theorem polyTimeComputable_initial : PolyTimeComputable fun x => state x 0 0 := by
  simpa only [state_eq] using polyTimeComputable_id.pairEncode
    ((polyTimeComputable_const (Nat.bits 0)).pairEncode
      (polyTimeComputable_const (Nat.bits 0)))

/-- Through the terminal rank, the state has linear width in the input and
seed length: `|state x i a| ≤ 2|x|+3m+7` if `a ≤ i ≤ 2^m`.
[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, final paragraph of the proof] -/
theorem length_state_le (x : List Bool) (m i a : ℕ) (hi : i ≤ 2 ^ m) (ha : a ≤ i) :
    (state x i a).length ≤ 2 * x.length + 3 * m + 7 := by
  have hlen (j : ℕ) (hj : j ≤ 2 ^ m) : (Nat.bits j).length ≤ m + 1 := by
    apply LogProg.length_bits_le
    have hp : 0 < 2 ^ m := Nat.two_pow_pos m
    rw [pow_succ]
    omega
  have hi' := hlen i hi
  have ha' := hlen a (ha.trans hi)
  rw [state_eq, length_pairEncode, length_pairEncode]
  omega

end Complexity.SeedMajority
