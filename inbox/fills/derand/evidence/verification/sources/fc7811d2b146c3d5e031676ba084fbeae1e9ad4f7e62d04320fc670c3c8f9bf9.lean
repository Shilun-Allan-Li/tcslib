/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
import TCSlib.Complexity.Randomized.BPPHard
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Consequences of BPP = P

[AB09, p.135 and §7.5.3, p.138]: if `BPP = P`, then `BPP ⊊ DTIME(n^{log n})`, and `BPP` has
a complete problem "since `P` does" (every nontrivial language of `P` is `P`-complete).

## Main definitions

* `Randomized.emptyWordLang` — `{ε}`.

## Main results

* `Randomized.polyTimeReducible_of_mem_P` — `P` reduces to every nontrivial language.
* `Randomized.not_polyTimeReducible_empty`, `Randomized.not_polyTimeReducible_univ`.
* `Randomized.BPP_PTM_ssubset_DTIME_pow_log_of_eq_P` — [AB09, p.135].
* `Randomized.exists_BPPHard_mem_BPP_PTM_of_eq_P` — [AB09, §7.5.3, p.138].

## Divergences

* `BPP` is `Randomized.BPP_PTM` ([AB09, Def 7.2]); completeness is membership plus
  `Randomized.BPPHard` (Karp reductions `≤ₚ`, [AB09, Def 2.7]); `log = Nat.log 2`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Turing Complexity

/-- **Every nontrivial `L` is `P`-hard**, via `x ↦ if x ∈ L' then a else b`.
[AB09, §7.5.3, p.138] -/
theorem polyTimeReducible_of_mem_P {L L' : Language Bool} (hL' : L' ∈ P) {a b : List Bool}
    (ha : a ∈ L) (hb : b ∉ L) : L' ≤ₚ L := by
  have hp := mem_P_iff_polyTimeComputable.mp hL'
  refine ⟨fun x => if MultiTapeTM.indicator L' x then a else b,
    polyTimeComputable_ite hp (polyTimeComputable_const a) (polyTimeComputable_const b),
    fun x => ?_⟩
  by_cases hx : x ∈ L' <;> simp [MultiTapeTM.indicator, hx, ha, hb]

/-- `∅` is not `P`-hard (`{0,1}* ∈ P` by `Complexity.univ_mem_P`). -/
theorem not_polyTimeReducible_empty :
    ¬ (Set.univ : Language Bool) ≤ₚ ((∅ : Set (List Bool)) : Language Bool) := by
  rintro ⟨f, -, hf⟩
  exact ((hf []).mp (Set.mem_univ _)).elim

/-- `{0,1}*` is not `P`-hard (`∅ ∈ P` by `Complexity.empty_mem_P`). -/
theorem not_polyTimeReducible_univ :
    ¬ ((∅ : Set (List Bool)) : Language Bool) ≤ₚ Set.univ := by
  rintro ⟨f, -, hf⟩
  exact ((hf []).mpr (Set.mem_univ _)).elim

/-- The language `{ε}` of the empty word. -/
def emptyWordLang : Language Bool := {x | x = []}

/-- `{ε} ∈ P`. -/
theorem emptyWordLang_mem_P : emptyWordLang ∈ P := by
  refine mem_P_iff_polyTimeComputable.mpr ?_
  convert polyTimeComputable_isNil using 1
  funext x
  by_cases hx : x = [] <;> simp [MultiTapeTM.indicator, emptyWordLang, hx]

/-- **`{ε}` is `P`-hard.** [AB09, §7.5.3, p.138] -/
theorem polyTimeReducible_emptyWordLang {L' : Language Bool} (hL' : L' ∈ P) :
    L' ≤ₚ emptyWordLang :=
  polyTimeReducible_of_mem_P hL' (a := []) (b := [true]) rfl (fun h => List.cons_ne_nil _ _ h)

/-- **If `BPP = P` then `BPP` has a complete problem** [AB09, §7.5.3, p.138]. -/
theorem exists_BPPHard_mem_BPP_PTM_of_eq_P (h : BPP_PTM = P) :
    ∃ L ∈ BPP_PTM, BPPHard L := by
  refine ⟨emptyWordLang, h ▸ emptyWordLang_mem_P, fun L' hL' => ?_⟩
  exact polyTimeReducible_emptyWordLang (h ▸ hL')

/-- **If `BPP = P` then `BPP ⊊ DTIME(n^{log n})`** [AB09, §7.5, p.135]. -/
theorem BPP_PTM_ssubset_DTIME_pow_log_of_eq_P (h : BPP_PTM = P) :
    BPP_PTM ⊂ DTIME (fun n => n ^ Nat.log 2 n) :=
  h ▸ P_ssubset_DTIME_pow_log

end Randomized
