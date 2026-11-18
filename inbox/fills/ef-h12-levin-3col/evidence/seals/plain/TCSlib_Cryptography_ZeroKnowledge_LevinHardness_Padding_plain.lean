/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD TCSlib.Cryptography.ProperColoring TCSlib.Cryptography.ThreeColorable TCSlib.Cryptography.encColoring TCSlib.Cryptography.encGraph TCSlib.Cryptography.EncodingMachines.divNum TCSlib.Cryptography.EncodingMachines.modNum

/-!
# Padding graphs and colourings to an exact vertex count

The Levin reduction to `3COL` ([AB09, §2.3]; [PS10, §4.7, Theorem 124.1, step 2]) is assembled
from maps whose output graphs should have an exact, length-determined number of vertices `B`.
This file pads a graph `G : Graph n` with isolated vertices to `padGraph G B : Graph B` and a
colouring with colour `0` to `padColoring c B`, together with the string maps on encodings:
`padWord` on adjacency matrices (`encGraph`) and `padColWord` on colourings (`encColoring`),
both polynomial-time with `B` given in unary. Framework glue, no textbook counterpart.

## Main definitions

* `TCSlib.Cryptography.LevinHardness.padGraph` — `G` padded with isolated vertices to `B`.
* `TCSlib.Cryptography.LevinHardness.padColoring` — a colouring extended by colour `0`.
* `TCSlib.Cryptography.LevinHardness.padWord` — the padding on adjacency-matrix words.
* `TCSlib.Cryptography.LevinHardness.padColWord` — the padding on colouring words.

## Main results

* `TCSlib.Cryptography.LevinHardness.properColoring_padGraph`,
  `TCSlib.Cryptography.LevinHardness.threeColorable_padGraph_iff` — padding preserves proper
  colourings and (for `n ≤ B`) 3-colourability both ways.
* `TCSlib.Cryptography.LevinHardness.padWord_encGraph`,
  `TCSlib.Cryptography.LevinHardness.padColWord_encColoring` — the string maps encode the
  paddings.
* `TCSlib.Cryptography.LevinHardness.polyTimeComputable_padWord`,
  `TCSlib.Cryptography.LevinHardness.polyTimeComputable_padColWord` — they are polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7, Theorem 124.1, step 2.)
-/

namespace TCSlib.Cryptography.LevinHardness

open Complexity TCSlib.Cryptography.EncodingMachines

/-! ### Padding graphs and colourings -/

/-- **A graph padded with isolated vertices**: for `G : Graph n` and a vertex count `B`,
`padGraph G B u v = G u v` if `u, v < n` and `false` otherwise (for `B < n` the graph is
truncated to its first `B` vertices). -/
def padGraph {n : ℕ} (G : Graph n) (B : ℕ) : Graph B := fun u v =>
  if h : (u : ℕ) < n ∧ (v : ℕ) < n then G ⟨u, h.1⟩ ⟨v, h.2⟩ else false

/-- The entries of the padded graph:
`padGraph G B u v = if h : u < n ∧ v < n then G ⟨u, h.1⟩ ⟨v, h.2⟩ else false`. -/
theorem padGraph_apply {n : ℕ} (G : Graph n) (B : ℕ) (u v : Fin B) :
    padGraph G B u v =
      if h : (u : ℕ) < n ∧ (v : ℕ) < n then G ⟨u, h.1⟩ ⟨v, h.2⟩ else false := rfl

/-- **A colouring extended by colour `0`**: for `c : Fin n → Fin 3`,
`padColoring c B u = c u` if `u < n` and `0` otherwise. -/
def padColoring {n : ℕ} (c : Fin n → Fin 3) (B : ℕ) : Fin B → Fin 3 := fun u =>
  if h : (u : ℕ) < n then c ⟨u, h⟩ else 0

/-- The values of the padded colouring: `padColoring c B u = if h : u < n then c ⟨u, h⟩ else 0`. -/
theorem padColoring_apply {n : ℕ} (c : Fin n → Fin 3) (B : ℕ) (u : Fin B) :
    padColoring c B u = if h : (u : ℕ) < n then c ⟨u, h⟩ else 0 := rfl

/-- **Padding preserves proper colourings**: if `ProperColoring G c`, then
`ProperColoring (padGraph G B) (padColoring c B)` (every edge of the padded graph is an edge of
`G` between vertices `< n`, coloured by `c`; no hypothesis on `B` is needed). -/
theorem properColoring_padGraph {n : ℕ} {G : Graph n} {c : Fin n → Fin 3} (B : ℕ)
    (hc : ProperColoring G c) : ProperColoring (padGraph G B) (padColoring c B) := by
  rw [ProperColoring_iff] at hc ⊢
  intro u v huv
  rw [padGraph_apply] at huv
  by_cases h : (u : ℕ) < n ∧ (v : ℕ) < n
  · rw [dif_pos h] at huv
    rw [padColoring_apply, padColoring_apply, dif_pos h.1, dif_pos h.2]
    exact hc _ _ huv
  · rw [dif_neg h] at huv
    exact absurd huv Bool.false_ne_true

/-- **Padding preserves 3-colourability both ways**: for `n ≤ B`,
`ThreeColorable (padGraph G B) ↔ ThreeColorable G`. Forward: restrict a colouring of the padded
graph to the first `n` vertices; backward: `properColoring_padGraph`. -/
theorem threeColorable_padGraph_iff {n : ℕ} (G : Graph n) {B : ℕ} (hnB : n ≤ B) :
    ThreeColorable (padGraph G B) ↔ ThreeColorable G := by
  rw [threeColorable_iff, threeColorable_iff]
  constructor
  · rintro ⟨c', hc'⟩
    refine ⟨fun u => c' ⟨u, by omega⟩, ?_⟩
    rw [ProperColoring_iff] at hc' ⊢
    intro u v huv
    refine hc' ⟨u, by omega⟩ ⟨v, by omega⟩ ?_
    rw [padGraph_apply, dif_pos ⟨u.2, v.2⟩]
    exact huv
  · rintro ⟨c, hc⟩
    exact ⟨_, properColoring_padGraph B hc⟩

/-! ### Padding adjacency-matrix words -/

/-- **The graph padding on adjacency-matrix words**: with `n = ⌊√|w|⌋` (the vertex count read
by `decGraph`), `padWord w B` is the `B × B` word whose bit `k` (row `k / B`, column `k % B`) is
`[k / B < n] ∧ [k % B < n] ∧ w.getD (k % B + n (k / B)) false`. -/
def padWord (w : List Bool) (B : ℕ) : List Bool :=
  (List.range (B * B)).map fun k =>
    decide (k / B < Nat.sqrt w.length) && decide (k % B < Nat.sqrt w.length) &&
      w.getD (k % B + Nat.sqrt w.length * (k / B)) false

/-- The defining equation of `padWord`. -/
theorem padWord_eq (w : List Bool) (B : ℕ) :
    padWord w B = (List.range (B * B)).map fun k =>
      decide (k / B < Nat.sqrt w.length) && decide (k % B < Nat.sqrt w.length) &&
        w.getD (k % B + Nat.sqrt w.length * (k / B)) false := rfl

/-- **`padWord` encodes the padded graph**: `padWord (encGraph G) B = encGraph (padGraph G B)`
(for every `B`; for `B < n` both sides truncate).

**Proof sketch.** Both words have `B²` bits. Bit `m = (m % B) + B (m / B)` of the right side is
`padGraph G B (m / B) (m % B)` (`encGraph_getD_nat`, `Nat.mod_add_div`); on the left
`⌊√(n²)⌋ = n` (`length_encGraph`, `Nat.sqrt_eq`), and below `n` the bit is
`(encGraph G).getD (m % B + n (m / B)) false = G (m / B) (m % B)` (`encGraph_getD_nat`). -/
theorem padWord_encGraph {n : ℕ} (G : Graph n) (B : ℕ) :
    padWord (encGraph G) B = encGraph (padGraph G B) := by
  have hn : Nat.sqrt (encGraph G).length = n := by rw [length_encGraph, Nat.sqrt_eq]
  refine List.ext_getElem (by rw [padWord_eq, List.length_map, List.length_range,
    length_encGraph]) fun m h1 h2 => ?_
  have hm : m < B * B := by rwa [padWord_eq, List.length_map, List.length_range] at h1
  have hB : 0 < B := Nat.pos_of_ne_zero fun h => by simp [h] at hm
  have hu : m / B < B := (Nat.div_lt_iff_lt_mul hB).2 hm
  have hkey := encGraph_getD_nat (padGraph G B) ⟨m / B, hu⟩ ⟨m % B, Nat.mod_lt _ hB⟩
  rw [show m % B + B * (m / B) = m from Nat.mod_add_div m B, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some] at hkey
  rw [hkey, padGraph_apply]
  simp only [padWord_eq, List.getElem_map, List.getElem_range, hn]
  by_cases h : m / B < n ∧ m % B < n
  · rw [dif_pos h, ← encGraph_getD_nat G ⟨m / B, h.1⟩ ⟨m % B, h.2⟩]
    simp [h.1, h.2]
  · rw [dif_neg h]
    by_cases h' : m / B < n
    · have h'' : ¬ m % B < n := fun h'' => h ⟨h', h''⟩
      simp [h'']
    · simp [h']

/-- **The graph padding is polynomial-time** with the vertex count in unary:
`PolyTimeComputable fun z => padWord (pairFstD z) (pairSndD z).length`.

**Proof sketch.** Emit the bits `k < B²` with the tabulation host
`ComposeMachines.polyTimeComputable_flatMap_range` (`List.map_eq_flatMap`); bit `k` is a
conjunction (`polyTimeComputable_and`) of the unary comparisons `k / B < n`, `k % B < n`
(`EncodingMachines.ltTest_poly`, `EncodingMachines.divNum_poly`, `EncodingMachines.modNum_poly`
with their readers, `n = ⌊√|w|⌋` by `EncodingMachines.unarySqrt_poly`) and the bit of `w` at the
unary index `k % B + n (k / B)` (`EncodingMachines.getBit_poly`). The count `B²` is
`EncodingMachines.unaryMul_poly`. -/
theorem polyTimeComputable_padWord :
    PolyTimeComputable fun z => padWord (pairFstD z) (pairSndD z).length := by
  have hk : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hW : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hB : PolyTimeComputable fun w => List.replicate (pairSndD (pairSndD w)).length true :=
    unaryLength_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hn := unarySqrt_poly (unaryLength_poly hW)
  have hu : PolyTimeComputable fun w =>
      List.replicate ((pairFstD w).length / (pairSndD (pairSndD w)).length) true :=
    (divNum_poly hk hB).congr fun w => by rw [divNum_eq]
  have hv : PolyTimeComputable fun w =>
      List.replicate ((pairFstD w).length % (pairSndD (pairSndD w)).length) true :=
    (modNum_poly hk hB).congr fun w => by rw [modNum_eq]
  have hE := polyTimeComputable_and (polyTimeComputable_and (ltTest_poly hu hn)
    (ltTest_poly hv hn)) (getBit_poly hW (unaryAdd_poly hv (unaryMul_poly hn hu)))
  have hB0 : PolyTimeComputable fun z => List.replicate (pairSndD z).length true :=
    unaryLength_poly polyTimeComputable_pairSndD
  refine (SecureComputation.ComposeMachines.polyTimeComputable_flatMap_range
    (E := fun z k => [decide (k / (pairSndD z).length < Nat.sqrt (pairFstD z).length) &&
      decide (k % (pairSndD z).length < Nat.sqrt (pairFstD z).length) &&
      (pairFstD z).getD (k % (pairSndD z).length +
        Nat.sqrt (pairFstD z).length * (k / (pairSndD z).length)) false])
    hE (unaryMul_poly hB0 hB0)).congr fun z => ?_
  rw [padWord_eq, List.map_eq_flatMap]

/-! ### Padding colouring words -/

/-- **The colouring padding on words**: `padColWord w B = w ++ 0^(2B - |w|)` (two zero bits,
colour `0`, for each added vertex). Near-relative: `EncodingMachines.padTo (2B) w`, which agrees
with it when `|w| ≤ 2B`. -/
def padColWord (w : List Bool) (B : ℕ) : List Bool :=
  w ++ List.replicate (2 * B - w.length) false

/-- The defining equation of `padColWord`: `padColWord w B = w ++ 0^(2B - |w|)`. -/
theorem padColWord_eq (w : List Bool) (B : ℕ) :
    padColWord w B = w ++ List.replicate (2 * B - w.length) false := rfl

/-- **`padColWord` encodes the padded colouring**: for `n ≤ B`,
`padColWord (encColoring c) B = encColoring (padColoring c B)`.

**Proof sketch.** Both words have `2B` bits (`length_encColoring`). For a vertex `i < n` the
bits `2i, 2i + 1` come from `encColoring c` on both sides (`List.getD_append`,
`getD_encColoring_two_mul`, `getD_encColoring_two_mul_add_one`); for `n ≤ i < B` they are the
padding zeros on the left (`List.getD_append_right`, `List.getD_replicate`) and the two bits of
colour `0` on the right. -/
theorem padColWord_encColoring {n : ℕ} (c : Fin n → Fin 3) {B : ℕ} (hnB : n ≤ B) :
    padColWord (encColoring c) B = encColoring (padColoring c B) := by
  have hlen : (padColWord (encColoring c) B).length = B * 2 := by
    rw [padColWord_eq, List.length_append, List.length_replicate, length_encColoring]
    omega
  have hgetD : ∀ (l : List Bool) (m : ℕ) (h : m < l.length), l[m] = l.getD m false :=
    fun l m h => by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  refine List.ext_getElem (by rw [hlen, length_encColoring]) fun m h1 h2 => ?_
  rw [hgetD _ _ h1, hgetD _ _ h2, padColWord_eq]
  rw [hlen] at h1
  rcases Nat.even_or_odd' m with ⟨i, rfl | rfl⟩
  · have hr := getD_encColoring_two_mul (padColoring c B) ⟨i, by omega⟩
    rw [hr, padColoring_apply]
    by_cases hi : i < n
    · rw [List.getD_append _ _ _ _ (by rw [length_encColoring]; omega), dif_pos hi]
      exact getD_encColoring_two_mul c ⟨i, hi⟩
    · rw [List.getD_append_right _ _ _ _ (by rw [length_encColoring]; omega),
        List.getD_replicate _ (by rw [length_encColoring]; omega), dif_neg hi]
      decide
  · have hr := getD_encColoring_two_mul_add_one (padColoring c B) ⟨i, by omega⟩
    rw [hr, padColoring_apply]
    by_cases hi : i < n
    · rw [List.getD_append _ _ _ _ (by rw [length_encColoring]; omega), dif_pos hi]
      exact getD_encColoring_two_mul_add_one c ⟨i, hi⟩
    · rw [List.getD_append_right _ _ _ _ (by rw [length_encColoring]; omega),
        List.getD_replicate _ (by rw [length_encColoring]; omega), dif_neg hi]
      decide

/-- **The colouring padding is polynomial-time** with the vertex count in unary:
`PolyTimeComputable fun z => padColWord (pairFstD z) (pairSndD z).length` (append the zeros
`EncodingMachines.zeros_poly` of the unary length `2B - |w|`, `EncodingMachines.unarySub_poly`,
`EncodingMachines.unaryMul_poly`). -/
theorem polyTimeComputable_padColWord :
    PolyTimeComputable fun z => padColWord (pairFstD z) (pairSndD z).length :=
  (polyTimeComputable_pairFstD.append (EncodingMachines.zeros_poly
    (unarySub_poly (unaryMul_poly (unaryConst_poly 2)
      (unaryLength_poly polyTimeComputable_pairSndD))
      (unaryLength_poly polyTimeComputable_pairFstD)))).congr fun z => by rw [padColWord_eq]

end TCSlib.Cryptography.LevinHardness
