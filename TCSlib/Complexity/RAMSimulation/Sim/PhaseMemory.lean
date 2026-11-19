/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRegister

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Memory rows of an instruction phase

Keyed lookup and assignment run on memory tape zero, key tape one and one of the three word
registers. The encoding supplies their physical table, uniform widths and blank scratch.

## Main definitions

* `WordRAM.Sim.PhaseData`: word width, memory footprint, RAM configuration and tape origins.
* `WordRAM.Sim.phaseMemoryEntries`: a represented table chosen from an encoded frame.
* `WordRAM.Sim.phaseMemoryCost`: a footprint bound for one keyed memory operation.

## Main results

* `WordRAM.Sim.phase_memoryEntries_spec`: the chosen table represents the encoded memory.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing
open scoped Classical

/-- Semantic data supplied to an instruction row, independently of its finite control. -/
structure PhaseData where
  width : ℕ
  cells : Finset ℤ
  cfg : XCfg width
  origins : Fin 8 → ℤ

/-- Select a represented table when the frame encodes the semantic data, and the empty table
otherwise. This choice is only used to state the endpoint of a keyed assignment. -/
noncomputable def phaseMemoryEntries {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x) : List (List Bool × List Bool) :=
  if he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) then
    Classical.choose ((encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
      i.origins (F.cfg ())).mp he).2.1
  else []

/-- The selected table is the witness of the encoding's memory clause when that encoding holds,
and is empty otherwise. -/
theorem phaseMemoryEntries_eq {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x) :
    phaseMemoryEntries a fn i F =
      if he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) then
        Classical.choose ((encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
          i.origins (F.cfg ())).mp he).2.1
      else [] := rfl

/-- Under the row's encoding precondition, the selected entries have the physical keyed-table
layout and represent the indexed RAM memory. -/
theorem phase_memoryEntries_spec {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ())) :
    KeyTableAt (F.cfg ()) 0 (i.origins 0) (phaseMemoryEntries a fn i F) ∧
      TableOf a i.width i.cells i.cfg.mem (phaseMemoryEntries a fn i F) := by
  classical
  rw [phaseMemoryEntries_eq, dif_pos he]
  exact Classical.choose_spec ((encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
    i.origins (F.cfg ())).mp he).2.1

/-- A bound for the old table, key and value lengths in a single memory operation. -/
def phaseMemoryCost (a : ℕ) (i : PhaseData) : ℕ :=
  (1 + i.cells.card * (i.width + a + i.width + 4)) + (i.width + a) + i.width + 1

/-- The memory cost is the footprint layout bound plus one key, one word and one cell. -/
theorem phaseMemoryCost_eq (a : ℕ) (i : PhaseData) :
    phaseMemoryCost a i =
      (1 + i.cells.card * (i.width + a + i.width + 4)) + (i.width + a) + i.width + 1 := rfl

/-- The table/key/value bank places its value on register two, three or four and uses the two
dedicated scratch tapes. -/
def phaseMemoryBank (dst : Fin 3) : Fin 5 ↪ Fin 8 :=
  ⟨![0, 1, ⟨dst.val + 2, by omega⟩, 6, 7], by fin_cases dst <;> decide⟩

/-- The memory bank sends source indices to the table, key, selected value and scratch tapes. -/
theorem phaseMemoryBank_apply (dst : Fin 3) (r : Fin 5) :
    phaseMemoryBank dst r = ![0, 1, ⟨dst.val + 2, by omega⟩, 6, 7] r := rfl

/-- The RAM encoding and two register words supply every native keyed-row precondition on the
selected memory bank.

**Proof sketch.** Use `phase_memoryEntries_spec` for the shared chosen table and
`tableOf_widths` for its values. The selection lemmas transport layouts without changing their
heads; `phase_scratch_select` supplies the native scratch tapes. -/
theorem phase_memory_pre {S : Type} {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x) (q : S) (dst : Fin 3) (z : ℤ) (v : List Bool)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()))
    (hk : WordAt (F.cfg ()) 1 (keyBits a i.width z))
    (hv : WordAt (F.cfg ()) (phaseMemoryBank dst 2) v) (hlen : v.length = i.width) :
    let d := (F.cfg q).select (phaseMemoryBank dst)
    let es := phaseMemoryEntries a fn i F
    d.workTapePos 0 = i.origins 0 ∧ KeyTableAt d 0 (i.origins 0) es ∧
      WordAt d 1 (keyBits a i.width z) ∧ WordAt d 2 v ∧
      (∀ e ∈ es, e.2.length = v.length) ∧ ScratchBlank d := by
  have hh := (encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
    i.origins (F.cfg ())).mp he
  have hm := phase_memoryEntries_spec a fn i F he
  have hscratch : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (phaseMemoryBank dst r).val := by
    have hs : ∀ d : Fin 3, ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (phaseMemoryBank d r).val := by
      decide
    exact hs dst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Cfg.select_eq, PhaseFrame.cfg_eq, phaseMemoryBank_apply] using hh.1 0
  · apply (phase_keyTableAt_select (phaseMemoryBank dst) (F.cfg q) 0 (i.origins 0) _).mpr
    exact (phase_keyTableAt_congr (F.cfg ()) (F.cfg q) 0 (i.origins 0) _
      (by simp only [PhaseFrame.cfg_eq])).mp hm.1
  · apply (phase_wordAt_select (phaseMemoryBank dst) (F.cfg q) 1 _).mpr
    exact (phase_wordAt_frame F q 1 _).mpr hk
  · apply (phase_wordAt_select (phaseMemoryBank dst) (F.cfg q) 2 _).mpr
    exact (phase_wordAt_frame F q (phaseMemoryBank dst 2) v).mpr hv
  · intro e he'
    exact (tableOf_widths hm.2 e he').2.trans hlen.symm
  · exact phase_scratch_select (phaseMemoryBank dst) F q hscratch
      (phase_frame_scratch fn i.cells i.cfg i.origins F he)

/-- The actual table/key/value length charge is bounded by the semantic footprint cost. -/
theorem phase_memory_cost {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (ht : TableOf a W T m es)
    (i : PhaseData) (hW : W = i.width) (hT : T = i.cells) (z : ℤ)
    (v : List Bool) (hv : v.length = W) :
    keyTableLength es + (keyBits a W z).length + v.length + 1 ≤ phaseMemoryCost a i := by
  rw [keyBits_def, bvBits_length, hv, phaseMemoryCost_eq, ← hW, ← hT]
  have hl := phase_tableOf_layout_bound ht
  omega

/-- Keyed lookup writes the addressed RAM word to the selected word register, preserving all
other frame fields, within a constant times the footprint layout bound.

**Proof sketch.** Choose `exists_keyLookupTM` and the physical table from `Encodes`.
`tableOf_widths` supplies the native value widths, while `tableOf_keyLookup_default` identifies
the lookup result even for an absent zero cell. Place the row with `phase_wordRow` and increase
its allowance using `phase_tableOf_layout_bound`. -/
theorem phase_lookupRow (a : ℕ) (fn : Bool) (z : PhaseData → ℤ) (dst : Fin 3) :
    ∃ C : ℕ, Nonempty (PhaseRow (fun _ => PhaseData)
      (fun i F => Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
        WordAt (F.cfg ()) 1 (keyBits a i.width (z i)) ∧
        PhaseReady i.width (phaseMemoryBank dst 2) F ∧ InRange (i.width + a) (z i))
      (fun i F => F.write (phaseMemoryBank dst 2) (bvBits (i.cfg.mem (z i))))
      (fun i => C * phaseMemoryCost a i) (fun i => C * phaseMemoryCost a i)) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_keyLookupTM
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := fun _ => PhaseData) _ _ _ _ S M entry exit (phaseMemoryBank dst) 2
  intro x i F hp
  let es := phaseMemoryEntries a fn i F
  have hm := phase_memoryEntries_spec a fn i F hp.1
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff i.width (phaseMemoryBank dst 2) F).mp hp.2.2.1
  have hn := phase_memory_pre a fn i F entry dst (z i) w hp.1 hp.2.1 hw hwidth
  have hr := hM (i.origins 0) es (keyBits a i.width (z i)) w
    ((F.cfg entry).select (phaseMemoryBank dst))
    (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq])
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
  rw [hwidth, tableOf_keyLookup_default hm.2 hp.2.2.2] at hr
  have hcost : keyTableLength es + (keyBits a i.width (z i)).length + i.width + 1 ≤
      phaseMemoryCost a i := by
    simpa only [List.length_replicate] using
      phase_memory_cost hm.2 i rfl rfl (z i) (List.replicate i.width false)
        (List.length_replicate ..)
  exact hr.mono (Nat.mul_le_mul_left C hcost) (Nat.mul_le_mul_left C hcost)

/-- The frame after assigning the value to the given RAM address in its represented table. -/
noncomputable def PhaseFrame.assign {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (z : ℤ) (v : BitVec i.width) (F : PhaseFrame x) : PhaseFrame x :=
  { F with
    workTapes := keyTableWrite (F.cfg ()) 0 (i.origins 0)
      (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width z) (bvBits v)) }

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.assign

/-- Assignment changes only the table tape by the layout of the updated selected entries. -/
theorem PhaseFrame.assign_eq {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (z : ℤ) (v : BitVec i.width) (F : PhaseFrame x) :
    F.assign a fn i z v =
      { F with
        workTapes := keyTableWrite (F.cfg ()) 0 (i.origins 0)
          (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width z) (bvBits v)) } := rfl

/-- Keyed assignment stores register four at the keyed address, within a constant times the
old semantic footprint's table/key/value charge.

**Proof sketch.** Use `phase_memory_pre` for the shared selected table and native preconditions.
`exists_keyAssignTM` gives the five-tape run and `phase_memory_cost` increases its bounds.
`phase_nativeRow` places that run, with `phase_embed_keyTableWrite` identifying the prescribed
assignment frame. -/
theorem phase_assignRow (a : ℕ) (fn : Bool) (z : PhaseData → ℤ)
    (v : (x : List Bool) → (i : PhaseData) → BitVec i.width) :
    ∃ C : ℕ, Nonempty (PhaseRow (fun _ => PhaseData)
      (fun {x} i F => Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
        WordAt (F.cfg ()) 1 (keyBits a i.width (z i)) ∧
        WordAt (F.cfg ()) 4 (bvBits (v x i)) ∧ InRange (i.width + a) (z i))
      (fun {x} i F => F.assign a fn i (z i) (v x i))
      (fun i => C * phaseMemoryCost a i) (fun i => C * phaseMemoryCost a i)) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_keyAssignTM
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_nativeRow (I := fun _ => PhaseData) _ _ _ _ S M entry exit (phaseMemoryBank 2)
    (fun {x} i F => { ((F.cfg entry).select (phaseMemoryBank 2)) with
      state := some exit
      workTapes := keyTableWrite ((F.cfg entry).select (phaseMemoryBank 2)) 0 (i.origins 0)
        (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width (z i)) (bvBits (v x i))) })
  · intro x i F hp
    have hn := phase_memory_pre a fn i F entry 2 (z i) (bvBits (v x i))
      hp.1 hp.2.1 hp.2.2.1 (bvBits_length _)
    have hr := hM (i.origins 0) (phaseMemoryEntries a fn i F) (keyBits a i.width (z i))
      (bvBits (v x i)) ((F.cfg entry).select (phaseMemoryBank 2))
      (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq])
      hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
    have hc := phase_memory_cost (phase_memoryEntries_spec a fn i F hp.1).2 i rfl rfl
      (z i) (bvBits (v x i)) (bvBits_length _)
    exact hr.mono (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left C hc)
  · intro x i F hp
    simpa only [PhaseFrame.assign_eq, PhaseFrame.cfg_eq, Cfg.select_eq,
      phase_keyTableWrite_as_update, phaseMemoryBank_apply] using
      phase_embed_keyTableWrite (phaseMemoryBank 2) (F.cfg entry) (some exit) F.inputPos 0
        (i.origins 0)
        (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width (z i)) (bvBits (v x i)))
  · intro x i F hp
    rfl

/-- A frame assignment preserves the encoding, updates its RAM word and adds the addressed cell
to the allowed footprint. -/
theorem phase_frame_assign_encodes {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()))
    (z : ℤ) (hz : InRange (i.width + a) z) (v : BitVec i.width) :
    Encodes a fn (insert z i.cells) { i.cfg with mem := Function.update i.cfg.mem z v }
      (Function.Embedding.refl _) i.origins ((F.assign a fn i z v).cfg ()) := by
  have hm := phase_memoryEntries_spec a fn i F he
  simpa only [PhaseFrame.assign_eq, PhaseFrame.cfg_eq] using
    phase_encodes_keyAssign fn i.cells i.cfg i.origins (F.cfg ()) he
      (phaseMemoryEntries a fn i F) hm.1 hm.2 z hz v

end WordRAM.Sim
