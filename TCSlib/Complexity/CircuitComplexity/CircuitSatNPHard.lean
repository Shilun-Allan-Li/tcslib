/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.UniformTableau
import TCSlib.Complexity.CircuitComplexity.CircuitSatReduction
import TCSlib.Complexity.CircuitComplexity.CircuitEvalNP
import TCSlib.Complexity.ClassNP.SAT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CKT-SAT is NP-hard, and the Cook–Levin theorem through circuits

[AB09, Lem 6.10]: `CKT-SAT` is `NP`-hard.  The book's proof: "the proof of Theorem 6.6
yields a polynomial-time transformation from `M, x` to a circuit `C` with `M(x, u) = C(u)`".
Here: for `L ∈ NP` with verifier `V ∈ P` (certificates of length `m(|x|) = C(|x| + 1)^c`,
`Complexity.NP`) decided by `M`, the reduction maps `x` to the description of the uniform
configuration tableau of `M` on the virtual input `x ++ u` — `x` hard-wired, the certificate
`u` the circuit's input (`Complexity.cfgTab M m x T`) — printed by the polynomial-time
emitter of [AB09, Remark 6.7] (`UniformTableauEmitterMain.lean`).  The circuit is satisfiable
iff some certificate makes `M` accept, i.e. iff `x ∈ L`.

[AB09, p. 111]: "The Cook–Levin Theorem follows immediately from the next two lemmas"
(Lem 6.10 and Lem 6.11, `CKT-SAT ≤p 3SAT`, `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`):
`3SAT` is `NP`-hard and `NP`-complete, and so is `SAT` (the Tseitin formulas are 3-CNFs, on
which `SAT` and `3SAT` agree).

## Main results

* `BoolCircuit.dagCktSatLang_NPHard` — CKT-SAT is `NP`-hard.  [AB09, Lem 6.10]
* `BoolCircuit.dagCktSatLang_NPComplete` — CKT-SAT is `NP`-complete.
* `Complexity.SAT3_NPHard_viaCircuits`, `Complexity.SAT3_NPComplete_viaCircuits`,
  `Complexity.SAT_NPHard_viaCircuits`, `Complexity.SAT_NPComplete_viaCircuits` — the
  Cook–Levin theorem [AB09, Thm 2.10], by Lem 6.10 and Lem 6.11 [AB09, p. 111].

## Divergences from [AB09]

* CKT-SAT is the language of descriptions (`DAGCircuit.encode`) of satisfiable fan-in-two
  circuits (`BoolCircuit.dagCktSatLang`); 3SAT and SAT are the library's
  (`Complexity.SAT3`, `Complexity.SAT`, over `Std.Sat.CNF.serialize`).
* The circuit is the non-oblivious configuration tableau (see `UniformTableau.lean`), of size
  `O(T(T + n + m))` for the verifier's time bound `T`.
* The declarations are named `…_viaCircuits` to keep them distinct from the
  `Complexity.SAT_NPHard`/`Complexity.SAT3_NPHard` of `CookLevin/Hardness.lean`, a separate
  campaign (the direct Cook–Levin reduction) in which those theorems are currently sorried;
  the `…_viaCircuits` theorems here are sorry-free.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§2.3, Theorem 2.10; §6.1.2, Lemmas 6.10 and 6.11,
  p. 111.)
-/

namespace BoolCircuit

open Complexity Turing

/-- The time bound `n + C(n + 1)^c + 1 ≤ (C + 1)(n + 1)^{c + 1}` raised to the verifier's degree. -/
private theorem verifier_time_le (n C c CV d : ℕ) :
    CV * (n + C * (n + 1) ^ c + 1) ^ d ≤ (CV * (C + 1) ^ d + 1) * (n + 1) ^ ((c + 1) * d) := by
  have h1 : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ (c + 1) := by
    have : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have : n + 1 ≤ (n + 1) ^ (c + 1) := Nat.le_self_pow (by omega) _
    nlinarith
  calc CV * (n + C * (n + 1) ^ c + 1) ^ d ≤ CV * ((C + 1) * (n + 1) ^ (c + 1)) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = CV * (C + 1) ^ d * (n + 1) ^ ((c + 1) * d) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ (CV * (C + 1) ^ d + 1) * (n + 1) ^ ((c + 1) * d) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- A list of length `m` is the list of its own bits. -/
private theorem ofFn_getD_eq (u : List Bool) {m : ℕ} (hu : u.length = m) :
    List.ofFn (fun i : Fin m => u.getD i false) = u := by
  subst hu
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- **[AB09, Lem 6.10]: CKT-SAT is NP-hard.**  Every language in `NP` Karp-reduces in
polynomial time to `BoolCircuit.dagCktSatLang`.

**Proof sketch.** Let `L ∈ NP` with certificates of length `m(x) = C(|x| + 1)^c` and verifier
`V` decided by `M` within `CV (N + 1)^d` steps.  Map `x` to the description of
`Complexity.cfgTab M m(x) x T(x)` — `M` on the virtual input `x ++ u` for `T(x)` steps, `x`
hard-wired and `u` the circuit's input — with `T(x) = (CV (C + 1)^d + 1)(|x| + 1)^{(c + 1)d}`
bounding the verifier's time on `x ++ u` (`verifier_time_le`).  The map is the emitter
(`Complexity.UTab.tabEmit`) after the polynomial-time front end
`x ↦ 1^{m(x)} 0 1^{T(x)} 0 x` (`Complexity.UTab.tabEmit_eq`).  The circuit has fan-in two,
and on `u` it outputs `1` iff `M` accepts `x ++ u` (`Complexity.cfgTab_eval`), so it is
satisfiable iff some certificate is accepted, i.e. iff `x ∈ L`. -/
theorem dagCktSatLang_NPHard : NPHard dagCktSatLang := by
  intro L hL
  obtain ⟨C, c, V, hV, hLV⟩ := hL
  obtain ⟨CV, d, M, hM⟩ := mem_P_iff.mp hV
  refine ⟨fun x => UTab.tabEmit M (List.replicate (C * (x.length + 1) ^ c) true ++ false ::
      (List.replicate ((CV * (C + 1) ^ d + 1) * (x.length + 1) ^ ((c + 1) * d)) true ++
        false :: x)),
    (UTab.polyTimeComputable_tabEmit M).comp (polyTimeComputable_tabInput
      (polyTimeComputable_polyUnary C c) (polyTimeComputable_polyUnary _ _)
      polyTimeComputable_id), fun x => ?_⟩
  set m := C * (x.length + 1) ^ c with hm
  set T := (CV * (C + 1) ^ d + 1) * (x.length + 1) ^ ((c + 1) * d) with hT
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the circuit decides the verifier on `x ++ u`
  have heval : ∀ v : Fin m → Bool, (Complexity.cfgTab M m x T).eval v =
      MultiTapeTM.indicator (V : Set (List Bool)) (x ++ List.ofFn v) := by
    intro v
    rw [cfgTab_eval]
    refine decide_emits_eq_of_computesInTime ((hM (x ++ List.ofFn v)).mono ?_)
    simp only [List.length_append, List.length_ofFn]
    exact verifier_time_le x.length C c CV d
  simp only
  rw [UTab.tabEmit_eq M m T x hT1, encode_mem_dagCktSatLang_iff, mem_dagCktSat_iff, hLV x]
  constructor
  · rintro ⟨u, hu, hxu⟩
    refine ⟨cfgTab_isFaninTwo M m x T, fun i => u.getD i false, ?_⟩
    rw [heval, ofFn_getD_eq u hu]
    simp [MultiTapeTM.indicator, hxu]
  · rintro ⟨-, v, hv⟩
    refine ⟨List.ofFn v, by simp [hm], ?_⟩
    rw [heval] at hv
    by_contra h
    simp [MultiTapeTM.indicator, h] at hv

/-- **CKT-SAT is NP-complete**: it is in `NP` (`BoolCircuit.dagCktSatLang_mem_NP`) and
`NP`-hard (`BoolCircuit.dagCktSatLang_NPHard`).  [AB09, §6.1.2] -/
theorem dagCktSatLang_NPComplete : NPComplete dagCktSatLang :=
  ⟨dagCktSatLang_mem_NP, dagCktSatLang_NPHard⟩

/-- The formula produced by the `CKT-SAT ≤p 3SAT` map is always a 3-CNF. -/
theorem dagCktSatToCNF_widthAtMost (w : List Bool) : (dagCktSatToCNF w).WidthAtMost 3 := by
  unfold dagCktSatToCNF
  split
  · split
    · exact DAGCircuit.toCNF_widthAtMost _
    · intro C hC; simp at hC; simp [hC]
  · intro C hC; simp at hC; simp [hC]

/-- On the outputs of the `CKT-SAT ≤p 3SAT` map, `SAT` and `3SAT` agree. -/
theorem mem_SAT_iff_mem_SAT3_dagCktSatToSAT3 (w : List Bool) :
    dagCktSatToSAT3 w ∈ Complexity.SAT ↔ dagCktSatToSAT3 w ∈ Complexity.SAT3 := by
  change (Std.Sat.CNF.decode _).Satisfiable ↔
    (Std.Sat.CNF.decode _).WidthAtMost 3 ∧ (Std.Sat.CNF.decode _).Satisfiable
  rw [dagCktSatToSAT3, Std.Sat.CNF.decode_serialize]
  exact ⟨fun h => ⟨dagCktSatToCNF_widthAtMost w, h⟩, fun h => h.2⟩

end BoolCircuit

namespace Complexity

open BoolCircuit

/-- **The Cook–Levin theorem through circuits: 3SAT is NP-hard** [AB09, p. 111: "The
Cook–Levin Theorem follows immediately from the next two lemmas"]: every `NP` language
reduces to CKT-SAT (`BoolCircuit.dagCktSatLang_NPHard`, [AB09, Lem 6.10]), which reduces to
3SAT (`BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, [AB09, Lem 6.11]); Karp reductions
compose ([AB09, Thm 2.8]). -/
theorem SAT3_NPHard_viaCircuits : NPHard SAT3 :=
  fun L hL => (dagCktSatLang_NPHard L hL).trans dagCktSatLang_polyTimeReducible_SAT3

/-- **3SAT is NP-complete** [AB09, Thm 2.10], via [AB09, Lem 6.10, Lem 6.11]: it is in `NP`
(`Complexity.SAT3_mem_NP`) and `NP`-hard (`Complexity.SAT3_NPHard_viaCircuits`). -/
theorem SAT3_NPComplete_viaCircuits : NPComplete SAT3 :=
  ⟨SAT3_mem_NP, SAT3_NPHard_viaCircuits⟩

/-- **SAT is NP-hard** [AB09, Thm 2.10], via [AB09, Lem 6.10, Lem 6.11]: the `CKT-SAT ≤p 3SAT`
map produces 3-CNFs, on which `SAT` and `3SAT` agree, so it also reduces CKT-SAT to `SAT`. -/
theorem SAT_NPHard_viaCircuits : NPHard SAT := by
  intro L hL
  refine (dagCktSatLang_NPHard L hL).trans ⟨dagCktSatToSAT3,
    polyTimeComputable_dagCktSatToSAT3, fun w => ?_⟩
  rw [mem_SAT_iff_mem_SAT3_dagCktSatToSAT3]
  exact mem_dagCktSatLang_iff_mem_SAT3 w

/-- **The Cook–Levin theorem: SAT is NP-complete** [AB09, Thm 2.10], via
[AB09, Lem 6.10, Lem 6.11]. -/
theorem SAT_NPComplete_viaCircuits : NPComplete SAT :=
  ⟨SAT_mem_NP, SAT_NPHard_viaCircuits⟩

end Complexity
