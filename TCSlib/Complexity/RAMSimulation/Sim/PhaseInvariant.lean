/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Preservation of the RAM encoding by instruction rows

Register writes preserve the represented memory, and a keyed assignment updates exactly one
cell. The invariant includes the word registers, input-length word, blank scratch tapes and
mode-dependent output, so these preservation facts can be used between every pair of rows.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_encodes_mono`: enlarge the allowed footprint without changing tape data.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Enlarging the allowed memory footprint preserves the encoded configuration. -/
theorem phase_encodes_mono {K a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T U : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ)
    (d : Turing.Cfg K Bool S x) (he : Encodes a fn T c σ o d) (hTU : T ⊆ U) :
    Encodes a fn U c σ o d := by
  obtain ⟨h₀, ⟨es, h₁, h₂⟩, h₃, h₄, h₅, h₆, h₇⟩ := (encodes_iff a fn T c σ o d).mp he
  exact (encodes_iff a fn U c σ o d).mpr
    ⟨h₀, ⟨es, h₁, tableOf_mono h₂ hTU⟩, h₃, h₄, h₅, h₆, h₇⟩

/-- Writing a word of the prescribed width into any of the four registers preserves the
encoded RAM configuration.

**Proof sketch.** Read the seven clauses of `encodes_iff`. The written register has its new
word by `phase_wordAt_write`; every other tape is unchanged by `phase_wordWrite_as_update`
and `Function.update_of_ne`. The represented table and blank scratch tapes are therefore
preserved, as are all heads and the output. -/
theorem phase_encodes_wordWrite {a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o d) (r : Fin 8)
    (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) (w : List Bool)
    (hw : w.length = if r = 1 then W + a else W) :
    Encodes a fn T c (Function.Embedding.refl _) o
      { d with workTapes := wordWrite d r w } := by
  obtain ⟨hpos, ⟨es, htable, hmem⟩, hkey, hregs, hlen, hscratch, hout⟩ :=
    (encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he
  have same (j : Fin 8) (hj : j ≠ r) : wordWrite d r w j = d.workTapes j := by
    rw [phase_wordWrite_as_update, Function.update_of_ne hj]
  have keep {j : Fin 8} {v : List Bool} (hj : j ≠ r) (hv : WordAt d j v) :
      WordAt { d with workTapes := wordWrite d r w } j v := by
    exact (phase_wordAt_congr d { d with workTapes := wordWrite d r w } j v
      (same j hj).symm rfl).mp hv
  apply (encodes_iff a fn T c (Function.Embedding.refl _) o _).mpr
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, hout⟩
  · refine ⟨es, ?_, hmem⟩
    exact (phase_keyTableAt_congr d _ 0 (o 0) es
      (same 0 (by intro h; have := congrArg Fin.val h; omega)).symm).mp htable
  · by_cases hr : r = 1
    · subst r
      rw [if_pos rfl] at hw
      obtain ⟨v, hv, hvlen⟩ := hkey
      exact ⟨w, phase_wordAt_write d 1 v w hv (hw.trans hvlen.symm), hw⟩
    · obtain ⟨v, hv, hvlen⟩ := hkey
      exact ⟨v, keep (Ne.symm hr) hv, hvlen⟩
  · intro j hj₀ hj₁
    by_cases hj : j = r
    · subst j
      have hr : r ≠ 1 := by intro h; have := congrArg Fin.val h; omega
      rw [if_neg hr] at hw
      obtain ⟨v, hv, hvlen⟩ := hregs r hj₀ hj₁
      exact ⟨w, phase_wordAt_write d r v w hv (hw.trans hvlen.symm), hw⟩
    · obtain ⟨v, hv, hvlen⟩ := hregs j hj₀ hj₁
      exact ⟨v, keep hj hv, hvlen⟩
  · exact keep (j := 5) (by intro h; have := congrArg Fin.val h; omega) hlen
  · intro j hj q
    change wordWrite d r w j q = none
    rw [same j (by intro h; have := congrArg Fin.val h; omega)]
    exact hscratch j hj q

/-- A keyed assignment to an in-range cell preserves the full encoding, updates that cell's
memory word, and adds the cell to the allowed footprint.

**Proof sketch.** `phase_keyTableAt_write` and `phase_keyAssign_layout_mono` establish the new
physical table; `tableOf_keyAssign` establishes its memory meaning. All other tapes are framed
by `phase_keyTableWrite_as_update` and `Function.update_of_ne`, so their words and scratch
blankness are preserved. Heads and output do not change. -/
theorem phase_encodes_keyAssign {a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o d)
    (es : List (List Bool × List Bool)) (htable : KeyTableAt d 0 (o 0) es)
    (hmem : TableOf a W T c.mem es) (z : ℤ) (hz : InRange (W + a) z) (v : BitVec W) :
    Encodes a fn (insert z T) { c with mem := Function.update c.mem z v }
      (Function.Embedding.refl _) o
      { d with workTapes := keyTableWrite d 0 (o 0) (keyAssign es (keyBits a W z) (bvBits v)) } := by
  obtain ⟨hpos, _, hkey, hregs, hlen, hscratch, hout⟩ :=
    (encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he
  let es' := keyAssign es (keyBits a W z) (bvBits v)
  let d' := { d with workTapes := keyTableWrite d 0 (o 0) es' }
  have same (j : Fin 8) (hj : j ≠ 0) : keyTableWrite d 0 (o 0) es' j = d.workTapes j := by
    rw [phase_keyTableWrite_as_update, Function.update_of_ne hj]
  have keep {j : Fin 8} {w : List Bool} (hj : j ≠ 0) (hw : WordAt d j w) :
      WordAt d' j w :=
    (phase_wordAt_congr d d' j w (same j hj).symm rfl).mp hw
  apply (encodes_iff a fn (insert z T) { c with mem := Function.update c.mem z v }
    (Function.Embedding.refl _) o d').mpr
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, hout⟩
  · exact ⟨es', phase_keyTableAt_write d 0 (o 0) es es' htable
      (phase_keyAssign_layout_mono hmem hz v), tableOf_keyAssign hmem hz v⟩
  · obtain ⟨w, hw, hwidth⟩ := hkey
    exact ⟨w, keep (j := 1) (by decide) hw, hwidth⟩
  · intro j hj₀ hj₁
    obtain ⟨w, hw, hwidth⟩ := hregs j hj₀ hj₁
    exact ⟨w, keep (j := j) (by intro h; have := congrArg Fin.val h; omega) hw, hwidth⟩
  · exact keep (j := 5) (by decide) hlen
  · intro j hj q
    change keyTableWrite d 0 (o 0) es' j q = none
    rw [same j (by intro h; have := congrArg Fin.val h; omega)]
    exact hscratch j hj q

end WordRAM.Sim
