/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The aggregated block tests

The three customers of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): the one-bit OR,
strict-majority, and XOR-then-OR aggregations of a polynomial-time one-bit
indicator over polynomially many polynomial-length blocks are polynomial-time.
Each is an instance of the countdown block loop `Complexity.BlockLoop`
(`PolyTimeBlockLoop`), with the aggregation state (flag, vote counters, XOR mask)
carried inside the loop's state word.  The XOR-then-OR test is an instance of the
OR-flag engine `Complexity.BlockLoop.polyTimeComputable_orLoop`, supplying its per-round
test, its remainder update and the closed form of its remainders; the plain OR test is
the XOR-then-OR test with an all-`false` mask.

These are the `PolyTimeComputable` engines of the `P`-closure lemmas
`Complexity.mem_P_of_blockAny` / `_blockMajority` / `_blockXorAny` in
`TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.blockAt` — the `i`-th length-`a·(n+1)^k` block of the second
  component of a pair, where `n` is the first component's length.

## Main results

* `Complexity.BlockLoop.polyTimeComputable_orLoop` — the OR-flag block loop is
  polynomial-time, and its output is the OR of the per-round tests.
* `Complexity.polyTimeComputable_blockAnyTest` / `_blockXorAnyTest` — the
  aggregated one-bit OR and XOR-then-OR block tests of a polynomial-time
  one-bit indicator are polynomial-time.  The strict-majority test lives in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockMajority`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.14–7.15: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-- The `i`-th length-`a·(n+1)^k` block of the second component of a pair,
where `n` is the first component's length. -/
def blockAt (a k : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
    (a * ((pairFstD z).length + 1) ^ k)

/-! #### The OR-flag block loop -/

namespace BlockLoop

/-- Replacing a nonempty word by the flag `[true]` does not lengthen it. -/
theorem length_flag_le {f : List Bool} (hf : f ≠ []) (b : Bool) :
    (if b then [true] else f).length ≤ f.length := by
  cases b
  · simp
  · simpa using List.length_pos_of_ne_nil hf

/-- One OR round: raising the flag on the `i`-th test value extends the flag
`[(range i).any F]` to `[(range (i+1)).any F]`. -/
theorem any_range_succ_flag (F : ℕ → Bool) (i : ℕ) :
    (if F i then [true] else [(List.range i).any F]) = [(List.range (i + 1)).any F] := by
  rw [List.range_succ, List.any_append]
  cases h : F i <;> simp [h]

/-- **An OR-flag block loop computes the OR of its tests in polynomial time.**  Run from
`⟨[false], ⟨1^K z, r z⟩⟩`, `K z = a'·(|x z|+1)^k'`, the loop raising its flag when `t` holds
of the remainder and advancing the remainder by `nxt`.  If the remainders follow `Q z`
(`r z = Q z 0`, `nxt (Q z i) = Q z (i+1)`), `t (Q z i) = F z i`, `|nxt q| ≤ |q| + 2 + c`,
`|x z| ≤ |r z|`, and `t`, `nxt`, `x`, `r` are polynomial-time, then so is
`z ↦ [(range (K z)).any (F z)]`.
**Proof sketch.** `polyTimeComputable_countdown` with the flag update and `out = pairFstD`;
`loop_output` at heads `[(range i).any (F z)]`, by `any_range_succ_flag`. -/
theorem polyTimeComputable_orLoop {t : List Bool → Bool} {nxt x r : List Bool → List Bool}
    (Q : List Bool → ℕ → List Bool) {F : List Bool → ℕ → Bool} (a' k' c : ℕ)
    (ht : PolyTimeComputable (fun s => [t (pairSndD (pairSndD s))]))
    (hn : PolyTimeComputable (fun s => nxt (pairSndD (pairSndD s))))
    (hx : PolyTimeComputable x) (hr : PolyTimeComputable r)
    (hnlen : ∀ q, (nxt q).length ≤ q.length + 2 + c)
    (hxr : ∀ z, (x z).length ≤ (r z).length)
    (hQ0 : ∀ z, r z = Q z 0)
    (hadv : ∀ z i, i < a' * ((x z).length + 1) ^ k' → nxt (Q z i) = Q z (i + 1))
    (htest : ∀ z i, i < a' * ((x z).length + 1) ^ k' → t (Q z i) = F z i) :
    PolyTimeComputable (fun z => [(List.range (a' * ((x z).length + 1) ^ k')).any (F z)]) := by
  refine polyTimeComputable_countdown
    (g := step (fun h q => if t q then [true] else h) (fun _ q => nxt q)) (out := pairFstD)
    rfl rfl [false] a' k' c (polyTimeComputable_ite ht (polyTimeComputable_const [true])
      polyTimeComputable_pairFstD) hn polyTimeComputable_pairFstD hx hr
    (fun h q hh => by
      have := length_flag_le hh (t q)
      have := hnlen q
      omega) (fun z => ?_)
  have hlen : (x z).length ≤ (pairEncode [false] (pairEncode
      (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))).length := by
    have := hxr z
    simp only [length_pairEncode]
    omega
  have hout := loop_output
    (g := step (fun h q => if t q then [true] else h) (fun _ q => nxt q)) (out := pairFstD)
    (s₀ := pairEncode [false] (pairEncode
      (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z)))
    rfl (fun i => [(List.range i).any (F z)]) (Q z) (by simp [hQ0 z]) (fun _ _ => by simp)
    (fun i hi => by simp only [htest z i hi]; exact any_range_succ_flag (F z) i)
    (fun i hi => hadv z i hi) (lt_polyBudget_of_le a' k' hlen)
  rw [hout, pairFstD_pairEncode]

end BlockLoop

/-! #### The XOR-then-OR test -/

/-- The XOR-then-OR aggregated block test of a polynomial-time one-bit
indicator is polynomial-time: the input is a nested pair
`⟨⟨x, u⟩, v⟩`; block `i` is drawn from `u`, XORed bitwise with `v`
(truncating, `Complexity.xorD`), and tested paired with `x`.

**Proof sketch.** An instance of `Complexity.BlockLoop.polyTimeComputable_orLoop` on
the remainder `⟨v, ⟨x, u⟩⟩`: the round's test input is
`pairEncode x (xorD (pairEncode v block))` (`Complexity.polyTimeComputable_xorD`,
`Complexity.xorD_pairEncode`), the mask `v` is carried unchanged, and the block is
dropped from `u`. -/
theorem polyTimeComputable_blockXorAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun w =>
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) := by
  have hzzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hmask : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hx : PolyTimeComputable (fun w => pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  exact BlockLoop.polyTimeComputable_orLoop
    (t := fun q => MultiTapeTM.indicator V (pairEncode (pairFstD (pairSndD q))
      (xorD (pairEncode (pairFstD q) (pairSndD (sliceTakeAt a k (pairSndD q)))))))
    (nxt := fun q => pairEncode (pairFstD q) (sliceDropAt a k (pairSndD q)))
    (fun w i => pairEncode (pairSndD w) (pairEncode (pairFstD (pairFstD w))
      ((pairSndD (pairFstD w)).drop (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))))
    a' k' 2
    (hV.comp ((polyTimeComputable_pairFstD.comp hzzz).pairEncode
      (polyTimeComputable_xorD.comp (hmask.pairEncode
        (polyTimeComputable_pairSndD.comp ((polyTimeComputable_sliceTakeAt a k).comp hzzz))))))
    (hmask.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzzz)) hx
    (polyTimeComputable_pairSndD.pairEncode
      (hx.pairEncode (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)))
    (fun q => by
      have := length_sliceDropAt_le a k (pairSndD q)
      have := length_pair_components_le q
      rw [length_pairEncode]
      omega)
    (fun w => by simp only [length_pairEncode]; omega)
    (fun w => by simp)
    (fun w i _ => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, BlockLoop.sliceDropAt_pairEncode_drop])
    (fun w i _ => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, BlockLoop.sliceTakeAt_pairEncode_drop,
        xorD_pairEncode]
      rfl)

/-! #### The OR test as the XOR test with a zero mask -/

/-- XOR of a word with itself is the all-`false` word of its length. -/
private theorem zipWith_xor_self (l : List Bool) :
    List.zipWith xor l l = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b l _ => simp [List.replicate_succ]

/-- XOR with an all-`false` mask of the block length leaves a block unchanged. -/
private theorem zipWith_xor_blockAt (a k : ℕ) (z : List Bool) (i : ℕ) :
    List.zipWith xor (List.replicate (a * ((pairFstD z).length + 1) ^ k) false)
      (blockAt a k z i) = blockAt a k z i := by
  have h : (blockAt a k z i).length ≤ a * ((pairFstD z).length + 1) ^ k :=
    List.length_take_le _ _
  generalize blockAt a k z i = l at h ⊢
  generalize a * ((pairFstD z).length + 1) ^ k = n at h ⊢
  induction l generalizing n with
  | nil => simp
  | cons b l ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [List.replicate_succ, List.zipWith_cons_cons, ih n (by simpa using h)]
      simp

/-- The OR-aggregated block test of a polynomial-time one-bit indicator is
polynomial-time: one bit saying whether some of the `a'·(n+1)^k'` blocks of
length `a·(n+1)^k` passes the test on `Turing.pairEncode`d (first component,
block).

**Proof sketch.** The XOR-then-OR test with an all-`false` mask of the block length:
on `⟨z, 0^B⟩`, where `B = a·(|x|+1)^k`, the XOR-shifted blocks are the blocks of `z`
themselves (each has length at most `B`), so this test is
`Complexity.polyTimeComputable_blockXorAnyTest` composed with `z ↦ ⟨z, 0^B⟩`.  The mask
`0^B` is computed as `xorD ⟨1^B, 1^B⟩` (`Complexity.polyTimeComputable_polyUnary`,
`Complexity.polyTimeComputable_xorD`). -/
theorem polyTimeComputable_blockAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) := by
  have hU : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have hpad := polyTimeComputable_id.pairEncode (polyTimeComputable_xorD.comp (hU.pairEncode hU))
  convert (polyTimeComputable_blockXorAnyTest hV a k a' k').comp hpad using 1
  funext z
  simp only [Function.comp, id, pairFstD_pairEncode, pairSndD_pairEncode, xorD_pairEncode,
    zipWith_xor_self, List.length_replicate, zipWith_xor_blockAt]

end Complexity
