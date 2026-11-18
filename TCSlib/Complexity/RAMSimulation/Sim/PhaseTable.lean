/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Memory-table invariants for instruction phases

The phase machines access a RAM cell through its two's-complement key. These lemmas connect
`Turing.keyLookup` and `Turing.keyAssign` to the memory represented by `TableOf`. Range
hypotheses are explicit: keys identify cells only within their signed range.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.keyBits_eq_iff`: equality of in-range keys is equality of cells.
* `WordRAM.Sim.tableOf_mono`, `WordRAM.Sim.tableOf_widths`, `WordRAM.Sim.tableOf_length_le`:
  footprint monotonicity, register widths and the entry-count bound.
* `WordRAM.Sim.tableOf_keyLookup`, `WordRAM.Sim.tableOf_keyLookup_default`: correct memory
  lookup, with the zero default used by the machine row.
* `WordRAM.Sim.phase_bvBits_zero`: the all-false representation of the zero word.
* `WordRAM.Sim.tableOf_keyAssign`: the memory invariant after an assignment.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9: memory represented by address-value pairs.)
-/

namespace WordRAM.Sim

open Turing

/-- Two cells in the signed key range have the same key exactly when they are equal.

**Proof sketch.** `bvBits_injective` recovers the words from their bit lists.
`WordRAM.toInt_wd` recovers each integer from its word, using the supplied range hypotheses. -/
theorem keyBits_eq_iff {a W : ℕ} {i j : ℤ} (hi : InRange (W + a) i)
    (hj : InRange (W + a) j) : keyBits a W i = keyBits a W j ↔ i = j := by
  constructor
  · intro h
    have hw := bvBits_injective (by simpa only [keyBits_def] using h)
    have he := congrArg BitVec.toInt hw
    exact (toInt_wd hi).symm.trans (he.trans (toInt_wd hj))
  · rintro rfl
    rfl

/-- Enlarging the allowed cell set preserves the memory represented by a table. -/
theorem tableOf_mono {a W : ℕ} {T U : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) (hTU : T ⊆ U) :
    TableOf a W U m es := by
  obtain ⟨hn, hs, hc⟩ := (tableOf_iff a W T m es).mp h
  refine (tableOf_iff a W U m es).mpr ⟨hn, ?_, hc⟩
  intro e he
  obtain ⟨z, hz, hr, heq⟩ := hs e he
  exact ⟨z, hTU hz, hr, heq⟩

/-- Every key in a represented memory has the key width, and every value has the word width. -/
theorem tableOf_widths {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) :
    ∀ e ∈ es, e.1.length = W + a ∧ e.2.length = W := by
  intro e he
  obtain ⟨z, _, _, rfl⟩ := ((tableOf_iff a W T m es).mp h).2.1 e he
  exact ⟨by rw [keyBits_def, bvBits_length], bvBits_length _⟩

/-- A represented memory table has at most as many entries as its allowed cell set.

**Proof sketch.** The distinct table keys form a finset with `es.length` elements by
`List.toFinset_card_of_nodup`. Entry soundness puts it inside the image of the allowed cell
set under `keyBits`; `Finset.card_le_card` and `Finset.card_image_le` give the bound. -/
theorem tableOf_length_le {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) : es.length ≤ T.card := by
  obtain ⟨hn, hs, _⟩ := (tableOf_iff a W T m es).mp h
  have hsub : (es.map Prod.fst).toFinset ⊆ T.image (keyBits a W) := by
    intro k hk
    obtain ⟨e, he, hek⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨z, hz, _, heq⟩ := hs e he
    refine Finset.mem_image.mpr ⟨z, hz, ?_⟩
    simpa only [heq] using hek
  calc
    es.length = (es.map Prod.fst).toFinset.card := by
      rw [List.toFinset_card_of_nodup hn, List.length_map]
    _ ≤ (T.image (keyBits a W)).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le

/-- Looking up a cell in the signed key range returns its memory word, defaulting to the
zero word when the cell has no stored entry.

**Proof sketch.** Read `keyLookup_def` and inspect the first matching entry. If it exists,
`TableOf` identifies its cell and `keyBits_eq_iff` identifies that cell with the query.
If it does not exist, the coverage clause of `TableOf` forces the query's memory word to be
zero, since any nonzero word would have supplied a matching key. -/
theorem tableOf_keyLookup {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) :
    (keyLookup es (keyBits a W z)).getD (bvBits (0 : BitVec W)) = bvBits (m z) := by
  obtain ⟨_, hs, hc⟩ := (tableOf_iff a W T m es).mp h
  rw [keyLookup_def]
  cases hf : es.find? (fun e => e.1 = keyBits a W z) with
  | none =>
    have hzero : m z = 0 := by
      by_contra hn
      obtain ⟨e, he, hek⟩ := List.mem_map.mp (hc z hz hn)
      have hnot := (List.find?_eq_none.mp hf) e he
      exact hnot (by simpa only [decide_eq_true_eq] using hek)
    rw [hzero]
    rfl
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hek : e.1 = keyBits a W z :=
      of_decide_eq_true (List.find?_some (p := fun e : List Bool × List Bool => e.1 = keyBits a W z) hf)
    obtain ⟨w, _, hw, heq⟩ := hs e he
    have hwz : w = z := (keyBits_eq_iff hw hz).mp (by simpa only [heq] using hek)
    subst w
    simp only [Option.map_some, Option.getD_some, heq]

/-- The bits of the zero word are precisely a word-width list of false bits. -/
theorem phase_bvBits_zero (W : ℕ) : bvBits (0 : BitVec W) = List.replicate W false := by
  have hz : (fun i : Fin W => (0 : BitVec W).getLsbD i.val) = fun _ => false := by
    funext i
    exact BitVec.getLsbD_zero
  rw [bvBits_def, hz, List.ofFn_const]

/-- The lookup row's all-false default returns exactly the queried memory word. -/
theorem tableOf_keyLookup_default {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) :
    (keyLookup es (keyBits a W z)).getD (List.replicate W false) = bvBits (m z) := by
  simpa only [phase_bvBits_zero] using tableOf_keyLookup h hz

/-! ## Assignment's list invariant -/

/-- Assignment retains precisely the entries with different keys, together with the new entry.

**Proof sketch.** Use `keyAssign_def`. When the key occurs, membership in the replacement map
is membership in an unchanged entry or in the inserted pair; the occurrence supplies a witness
for the inserted pair. When it does not occur, the definition appends that pair, and every old
entry has a different key. -/
private theorem phase_keyAssign_mem (es : List (List Bool × List Bool)) (k v : List Bool)
    (e : List Bool × List Bool) :
    e ∈ keyAssign es k v ↔ e = (k, v) ∨ e ∈ es ∧ e.1 ≠ k := by
  rw [keyAssign_def]
  split_ifs with h
  · obtain ⟨e₀, he₀, hk₀⟩ := List.any_eq_true.mp h
    have hk₀' : e₀.1 = k := of_decide_eq_true hk₀
    constructor
    · intro he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      split_ifs with hk
      · exact Or.inl rfl
      · exact Or.inr ⟨he', hk⟩
    · rintro (rfl | ⟨he, hk⟩)
      · exact List.mem_map.mpr ⟨e₀, he₀, if_pos hk₀'⟩
      · exact List.mem_map.mpr ⟨e, he, if_neg hk⟩
  · have hnone : ∀ e' ∈ es, e'.1 ≠ k := by
      intro e' he' hk
      apply h
      exact List.any_eq_true.mpr ⟨e', he', by simpa only [decide_eq_true_eq] using hk⟩
    constructor
    · intro he
      rcases List.mem_append.mp he with he | he
      · exact Or.inr ⟨he, hnone e he⟩
      · exact Or.inl (List.mem_singleton.mp he)
    · rintro (rfl | ⟨he, _⟩)
      · exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      · exact List.mem_append.mpr (Or.inl he)

/-- Assignment preserves distinct keys.

**Proof sketch.** In the replacement case the list of keys is unchanged. In the append case,
`List.any_eq_true` shows that the appended key was absent, so `List.nodup_append` applies. -/
private theorem phase_keyAssign_nodup (es : List (List Bool × List Bool)) (k v : List Bool)
    (hn : (es.map Prod.fst).Nodup) : ((keyAssign es k v).map Prod.fst).Nodup := by
  rw [keyAssign_def]
  split_ifs with h
  · have heq : (es.map (fun e => if e.1 = k then (k, v) else e)).map Prod.fst =
        es.map Prod.fst := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      by_cases hk : e.1 = k
      · simp only [Function.comp_apply, if_pos hk]
        exact hk.symm
      · simp only [Function.comp_apply, if_neg hk]
    rw [heq]
    exact hn
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨hn, ?_, ?_⟩
    · exact List.nodup_singleton k
    · intro a ha b hb hab
      have hb' : b = k := List.mem_singleton.mp hb
      rw [hab, hb'] at ha
      obtain ⟨e, he, hek⟩ := List.mem_map.mp ha
      apply h
      exact List.any_eq_true.mpr ⟨e, he, by simpa only [decide_eq_true_eq] using hek⟩

/-- Assigning an in-range cell preserves the represented memory, adding that cell to the
allowed footprint and updating its word.

**Proof sketch.** `phase_keyAssign_nodup` preserves distinct keys, and
`phase_keyAssign_mem` separates the new entry from unchanged entries with different keys.
`keyBits_eq_iff` turns different keys into different in-range cells, so the unchanged entries
remain sound for the updated memory. For coverage the assigned cell has its new entry;
every other nonzero cell keeps its old entry. -/
theorem tableOf_keyAssign {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) (v : BitVec W) :
    TableOf a W (insert z T) (Function.update m z v)
      (keyAssign es (keyBits a W z) (bvBits v)) := by
  obtain ⟨hn, hs, hc⟩ := (tableOf_iff a W T m es).mp h
  refine (tableOf_iff a W (insert z T) (Function.update m z v) _).mpr
    ⟨phase_keyAssign_nodup es _ _ hn, ?_, ?_⟩
  · intro e he
    rcases (phase_keyAssign_mem es _ _ e).mp he with heq | ⟨he, hne⟩
    · refine ⟨z, Finset.mem_insert_self _ _, hz, ?_⟩
      rw [heq, Function.update_self]
    · obtain ⟨y, hy, hyr, heq⟩ := hs e he
      have hyz : y ≠ z := by
        intro hyz
        apply hne
        rw [heq, hyz]
      refine ⟨y, Finset.mem_insert_of_mem hy, hyr, ?_⟩
      rw [heq, Function.update_of_ne hyz]
  · intro y hyr hnonzero
    by_cases hyz : y = z
    · subst y
      refine List.mem_map.mpr ⟨(keyBits a W z, bvBits v), ?_, rfl⟩
      exact (phase_keyAssign_mem es _ _ _).mpr (Or.inl rfl)
    · have hm : m y ≠ 0 := by
        simpa only [Function.update_of_ne hyz] using hnonzero
      obtain ⟨e, he, hek⟩ := List.mem_map.mp (hc y hyr hm)
      have hne : e.1 ≠ keyBits a W z := by
        intro hez
        exact hyz ((keyBits_eq_iff hyr hz).mp (hek.symm.trans hez))
      exact List.mem_map.mpr ⟨e, (phase_keyAssign_mem es _ _ e).mpr (Or.inr ⟨he, hne⟩), hek⟩

end WordRAM.Sim
