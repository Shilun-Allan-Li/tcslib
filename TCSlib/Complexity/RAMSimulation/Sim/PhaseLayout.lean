/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Address ranges and tape layouts of instruction phases

The memory-table invariant is used at the width of the keys. These lemmas extend the immediate
and computed address ranges to that width and bound the physical layout of a represented table.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_inRange_mono`: increasing the width preserves the signed range.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A cell in the signed range of a width is in the signed range of every larger width. -/
theorem phase_inRange_mono {m n : ℕ} {z : ℤ} (hmn : m ≤ n) (hz : InRange m z) :
    InRange n z := by
  have hp : (2 : ℤ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by omega) hmn
  obtain ⟨hl, hu⟩ := (inRange_iff m z).mp hz
  exact (inRange_iff n z).mpr ⟨by linarith, by linarith⟩

/-- The signed value of a word lies in the signed range of its width, including width zero. -/
theorem phase_toInt_inRange {W : ℕ} (u : BitVec W) : InRange W u.toInt := by
  exact (inRange_iff W u.toInt).mpr ⟨BitVec.le_two_mul_toInt, BitVec.two_mul_toInt_lt⟩

/-- A program immediate satisfying `ImmBound` lies in the range of the extended key width. -/
theorem phase_immediate_inRange {a W : ℕ} {ins : XInstr} (h : ImmBound a ins) {z : ℤ}
    (hz : z ∈ immediates ins) : InRange (W + a) z := by
  exact phase_inRange_mono (by omega) ((immBound_iff a ins).mp h z hz)

/-- A computed address, the signed value of a word, fits the extended key width. -/
theorem phase_computed_inRange {W : ℕ} (a : ℕ) (u : BitVec W) :
    InRange (W + a) u.toInt := by
  exact phase_inRange_mono (by omega) (phase_toInt_inRange u)

/-- Sign-extending a word writes exactly the key of its signed address. -/
theorem phase_keyBits_signExtend {W : ℕ} (a : ℕ) (u : BitVec W) :
    keyBits a W u.toInt = bvBits (u.signExtend (W + a)) := by
  rw [keyBits_def]
  apply congrArg bvBits
  apply BitVec.toInt_inj.mp
  rw [toInt_wd (phase_computed_inRange a u), BitVec.toInt_signExtend_of_le (by omega)]

/-- A keyed table with key width `K` and value width `V` occupies one header cell and
`K + V + 4` cells per entry, including markers and separators.

**Proof sketch.** Apply `joinFields_length` to the nonempty header-and-fields list read through
`tableFields_eq`. `keyFields_def` gives two marked fields per entry. The sum of their lengths
is `|es| * (K + V + 2)`, and there are `2 * |es|` separators after the header. -/
theorem phase_keyTableLength (es : List (List Bool × List Bool)) (K V : ℕ)
    (hw : ∀ e ∈ es, e.1.length = K ∧ e.2.length = V) :
    keyTableLength es = 1 + es.length * (K + V + 4) := by
  have hlen : (keyFields es).flatten.length = 2 * es.length := by
    simp only [keyFields_def, List.length_flatten, List.map_map, Function.comp_def,
      List.length_cons, List.length_nil, List.map_const', List.sum_replicate_nat]
    omega
  have hsum : ((keyFields es).flatten.map List.length).sum = es.length * (K + V + 2) := by
    simp only [keyFields_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, Nat.add_zero]
    calc
      _ = (es.map (fun _ => K + V + 2)).sum := by
        congr 1
        apply List.map_congr_left
        intro e he
        rw [(hw e he).1, (hw e he).2]
        omega
      _ = es.length * (K + V + 2) := by rw [List.map_const', List.sum_replicate_nat]
  have hne : tableFields [true] (keyFields es) ≠ [] := by
    rw [tableFields_eq]
    exact List.cons_ne_nil _ _
  rw [keyTableLength_def, joinFields_length _ hne, tableFields_eq]
  simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil,
    hlen, hsum]
  have h : 1 + es.length * (K + V + 2) + (2 * es.length + 1) - 1 =
      1 + es.length * (K + V + 2) + 2 * es.length := by omega
  rw [h]
  ring

/-- The physical layout of a represented memory is bounded by its allowed cell count. -/
theorem phase_tableOf_layout_bound {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) :
    keyTableLength es ≤ 1 + T.card * (W + a + W + 4) := by
  rw [phase_keyTableLength es (W + a) W (tableOf_widths h)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (tableOf_length_le h)) 1

/-- Key assignment never decreases the number of entries: it replaces values or appends. -/
theorem phase_keyAssign_length_le (es : List (List Bool × List Bool)) (k v : List Bool) :
    es.length ≤ (keyAssign es k v).length := by
  rw [keyAssign_def]
  split_ifs <;> simp only [List.length_map, List.length_append, List.length_cons,
    List.length_nil] <;> omega

/-- Assigning a word to an in-range memory cell never shrinks the physical table layout. -/
theorem phase_keyAssign_layout_mono {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) (v : BitVec W) :
    keyTableLength es ≤ keyTableLength (keyAssign es (keyBits a W z) (bvBits v)) := by
  rw [phase_keyTableLength es (W + a) W (tableOf_widths h),
    phase_keyTableLength _ (W + a) W (tableOf_widths (tableOf_keyAssign h hz v))]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (phase_keyAssign_length_le es _ _)) 1

/-- Replacing a keyed table by a layout at least as long preserves its tape representation,
including the blank right tail.

**Proof sketch.** Read `KeyTableAt` through `keyTableAt_iff` and `tableAt_iff`. Inside the new
layout `keyTableWrite_apply` supplies its cells. Left of the origin it preserves the two old
blank sentinels; from the new end onward it preserves the old blank tail. The nonshrinking
length premise places the latter region beyond the old end. -/
theorem phase_keyTableAt_write {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es es' : List (List Bool × List Bool)) (ht : KeyTableAt d r o es)
    (hlen : keyTableLength es ≤ keyTableLength es') :
    KeyTableAt { d with workTapes := keyTableWrite d r o es' } r o es' := by
  obtain ⟨ht, hb⟩ := (keyTableAt_iff d r o es).mp ht
  have ht' := (tableAt_iff d r o [true] (keyFields es)).mp ht
  have hc : (keyTableLength es : ℤ) ≤ (keyTableLength es' : ℤ) := by exact_mod_cast hlen
  apply (keyTableAt_iff _ r o es').mpr
  constructor
  · apply (tableAt_iff _ r o [true] (keyFields es')).mpr
    intro p hp hp'
    rw [← keyTableLength_def] at hp'
    change keyTableWrite d r o es' r (o + p) = fieldsTape (tableFields [true] (keyFields es')) p
    by_cases h0 : 0 ≤ p
    · by_cases hL : p < (keyTableLength es' : ℤ)
      · rw [keyTableWrite_apply, if_pos ⟨rfl, by omega, by omega⟩, add_sub_cancel_left]
      · rw [keyTableWrite_apply, if_neg (by omega), hb _ (by omega),
          fieldsTape_of_length_le _ (by rw [← keyTableLength_def]; omega)]
    · rw [keyTableWrite_apply, if_neg (by omega),
        ht' p hp (by rw [← keyTableLength_def]; omega), fieldsTape_of_neg _ (by omega),
        fieldsTape_of_neg _ (by omega)]
  · intro q hq
    change keyTableWrite d r o es' r q = none
    rw [keyTableWrite_apply, if_neg (by omega)]
    exact hb q (by omega)

end WordRAM.Sim
