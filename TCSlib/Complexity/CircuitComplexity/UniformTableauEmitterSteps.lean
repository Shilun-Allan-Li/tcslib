/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterLayer

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tableau emitter: all steps of the tableau

The snapshot of a step (`Complexity.UTab.goes_snap`), a whole step
(`Complexity.UTab.goes_layer`), and the loop over the `T + 1` steps
(`Complexity.UTab.goes_layers`): from the start of the tableau the emitter prints the gate
bits of all `(T + 1) · S` instructions of the uniform tableau circuit and reaches the final
template.

## Main results

* `Complexity.UTab.goes_snap`, `Complexity.UTab.goes_layer`, `Complexity.UTab.goes_layers`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6; §6.2, Remark 6.7.)
-/

namespace Complexity

namespace UTab

open Turing BoolCircuit CounterProg

variable (M : FinTM Bool) (x : List Bool) {n : ℕ} {z : List Bool} {T : ℕ}

/-- **The snapshot of a step**: the emitter prints its gates, then points `LB` at the next
step (clear it, copy `I`).

**Proof sketch.** The snapshot template (`goes_instr_inv`, `snap_bits`), the clear macro
on `LB` (`goes_clearR`) and the copy macro `I → LB` (`goes_copyR`). -/
theorem goes_snap {t : ℕ} (ht : t ≤ T) (e : ER) (hn : e.nc = n) (hz : e.z = z.length)
    (heT : e.t = T) (hi : e.i = snapIdx M (z.length + n) T t)
    (hq : e.q = if t = 0 then 0 else e.i - Str M n z T) (hlb : e.lb = t * Str M n z T)
    (htmp : e.tmp = 0) (ps : ℕ) :
    Goes (prog M) x (tpL (.snap (decide (t = 0)))) e.f ps
      (some (if decide (t = 0) then .cp .lt 0 else .hd .lay))
      { e with i := e.i + 1, q := if t = 0 then 0 else e.i + 1 - Str M n z T,
               lb := e.i + 1 }.f ps
      (ibits M n z T e.i) (Ki M + 2 * e.lb + 7 * (e.i + 1) + 3) := by
  have hS : t ≠ 0 → Str M n z T ≤ e.i := by
    intro h; rw [hi, snapIdx]
    have : 1 * Str M n z T ≤ t * Str M n z T := Nat.mul_le_mul_right _ (by omega)
    simp only [Str] at this ⊢; omega
  have s1 := goes_instr_inv M x (.snap (decide (t = 0))) rfl rfl e hq hS ps
  rw [snap_bits M ht e hn hz heT hi hlb] at s1
  have s2 := goes_clearR M x (.lb (decide (t = 0)))
    { e with i := e.i + 1, q := if t = 0 then 0 else e.i + 1 - Str M n z T } ps
  simp only [ClS.reg, ClS.exit, ER.f_lb, ER.set_lb] at s2
  have s3 := goes_copyR M x (.lb (decide (t = 0)))
    { e with i := e.i + 1, q := if t = 0 then 0 else e.i + 1 - Str M n z T, lb := 0 } ps
    (by simp [htmp])
  simp only [CpS.dst, CpS.src, ER.f_lb, ER.f_i, ER.set_lb, CpS.exit] at s3
  refine ((s1.trans s2).trans s3).congr rfl ?_ rfl rfl (by simp) ?_
  · congr 1
    ext <;> simp
  · simp only [hlb]; omega

/-- The register record at the start of step `t`: `I = LB = tS`, `Q = I − S` (or `0`), the
step counter `lt`, everything else `0` apart from `n`, `|z|` and `T`. -/
noncomputable def lstart (n : ℕ) (z : List Bool) (T t lt : ℕ) : ER :=
  ⟨n, z.length, T, t * Str M n z T, if t = 0 then 0 else t * Str M n z T - Str M n z T,
    t * Str M n z T, lt, 0, 0, 0, 0⟩

/-- The steps of one step of the tableau. -/
noncomputable def layerBound (n : ℕ) (z : List Bool) (T : ℕ) : ℕ :=
  M.k * ((2 * T + 3) * (Lmax M + 20)) + (z.length + n + 2) * (Lmax M + 20) + Ki M +
    9 * ((T + 1) * Str M n z T) + 6

/-- **One step of the tableau**: from the start of step `t` (`T ≥ 1`), the emitter prints the
gate bits of the instructions `tS, …, (t + 1)S − 1` — the cells of every tape, the input
positions, the snapshot — and reaches the step loop (after the first step, through the
copy of `T` into the step counter).

**Proof sketch.** `T ≠ 0` is tested; then `goes_tapes`, `goes_inputs`, `goes_snap`. -/
theorem goes_layer (hT : 1 ≤ T) {t : ℕ} (ht : t ≤ T) (lt : ℕ) (ps : ℕ) :
    Goes (prog M) x (.lay (decide (t = 0))) (lstart M n z T t lt).f ps
      (some (if decide (t = 0) then .cp .lt 0 else .hd .lay))
      { lstart M n z T (t + 1) lt with
        q := (if t = 0 then 0 else (t + 1) * Str M n z T - Str M n z T) }.f ps
      ((List.range' (t * Str M n z T) (Str M n z T)).flatMap (ibits M n z T))
      (layerBound M n z T) := by
  have s0 := goes_jz_pos (P := prog M) (x := x) (p := ps) (l := .lay (decide (t = 0)))
    (r := rT) (ρ := (lstart M n z T t lt).f) rfl (by simp [lstart]; omega)
  have s1 := goes_tapes M x (n := n) (z := z) hT ht M.k 0 (lstart M n z T t lt) (by omega)
    (by simp [lstart]) (by simp [lstart]) (by simp [lstart]) (by simp [lstart])
    (by simp [lstart]) (by simp [lstart]) (by simp [lstart]) (by simp [lstart]) ps
  have s2 := goes_inputs M x (n := n) (z := z) ht
    { lstart M n z T t lt with
      i := (lstart M n z T t lt).i + M.k * (2 * T + 1),
      q := if t = 0 then 0 else (lstart M n z T t lt).i + M.k * (2 * T + 1) - Str M n z T }
    (by simp [lstart]) (by simp [lstart]) (by simp [lstart]) (by simp) (by simp [lstart])
    (by simp [lstart]) (by simp [lstart]) (by simp [lstart]) (by simp [lstart]) ps
  have s3 := goes_snap M x (n := n) (z := z) ht
    { lstart M n z T t lt with
      i := (lstart M n z T t lt).i + M.k * (2 * T + 1) + (z.length + n + 2),
      q := if t = 0 then 0 else
        (lstart M n z T t lt).i + M.k * (2 * T + 1) + (z.length + n + 2) - Str M n z T }
    (by simp [lstart]) (by simp [lstart]) (by simp [lstart])
    (by simp [lstart, snapIdx, Str]; ring) (by simp) (by simp [lstart]) (by simp [lstart]) ps
  have hSv : Str M n z T = M.k * (2 * T + 1) + (z.length + n + 2) + 1 := by
    simp [Str, cfgStride]; ring
  have hall := ((s0.trans s1).trans s2).trans s3
  refine hall.congr rfl ?_ rfl rfl ?_ ?_
  · congr 1
    ext <;> simp [lstart] <;> (try split_ifs) <;> (try rw [hSv]) <;> ring_nf
  · have key : ∀ A, List.range' A (Str M n z T) = List.range' A (M.k * (2 * T + 1)) ++
        List.range' (A + M.k * (2 * T + 1)) (z.length + n + 2) ++
          [A + M.k * (2 * T + 1) + (z.length + n + 2)] := by
      intro A; rw [hSv, range'_add, range'_add]; simp; omega
    rw [key]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, lstart, List.nil_append]
  · simp only [layerBound, lstart]
    have h1 : t * Str M n z T ≤ (T + 1) * Str M n z T := Nat.mul_le_mul_right _ (by omega)
    rw [hSv] at h1 ⊢
    nlinarith

/-- After a step, the registers are those of the start of the next step. -/
theorem lstart_succ {t : ℕ} (lt : ℕ) :
    { lstart M n z T (t + 1) lt with
      q := (if t = 0 then 0 else (t + 1) * Str M n z T - Str M n z
          T) } = lstart M n z T (t + 1) lt := by
  ext <;> simp [lstart]
  intro h; subst h; simp

/-- A `range` of `a · S` elements is `a` consecutive blocks of `S`. -/
theorem range_mul (a S : ℕ) :
    List.range (a * S) = (List.range a).flatMap fun t => List.range' (t * S) S := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp [range'_eq_map]

/-- **All steps of the tableau**: from the start of the first step (`T ≥ 1`), the emitter
prints the gate bits of all `(T + 1) S` instructions and reaches the final template.

**Proof sketch.** The first step (`goes_layer`), the copy of `T` into the step counter, and the
step loop over steps `1, …, T` (`goes_layer` in the body). -/
theorem goes_layers (hT : 1 ≤ T) (ps : ℕ) :
    Goes (prog M) x (.lay true) (lstart M n z T 0 0).f ps (some (tpL .fin))
      (lstart M n z T (T + 1) 0).f ps
      ((List.range ((T + 1) * Str M n z T)).flatMap (ibits M n z T))
      ((T + 1) * (layerBound M n z T + 7 * T + 10)) := by
  have s1 := goes_layer M x (n := n) (z := z) hT (Nat.zero_le T) 0 ps
  rw [lstart_succ] at s1
  simp only [decide_true, if_true] at s1
  have s2 : Goes (prog M) x (.cp .lt 0) (lstart M n z T (0 + 1) 0).f ps (some (.hd .lay))
      (lstart M n z T 1 T).f ps [] (7 * T + 2) := by
    have := goes_copyR M x .lt (lstart M n z T (0 + 1) 0) ps (by simp [lstart])
    refine this.congr rfl ?_ rfl rfl rfl (by simp [CpS.src, lstart])
    rw [← ER.update_f]; funext r
    simp only [Function.update_apply, CpS.dst, CpS.src]
    split_ifs with h
    · subst h; simp [lstart]
    · fin_cases r <;> simp_all [lstart, ER.f]
  have s3 := goes_loop (P := prog M) (x := x) (head := .hd .lay) (dl := .dl .lay)
    (body := .lay false) (exit := tpL .fin) (r := rLT) (by simp [prog, Hd.reg, Hd.exit])
    (by simp [prog, Hd.reg, Hd.body]) T (fun j => (lstart M n z T (j + 1) (T - j)).f)
    (fun _ => ps) (fun j => (List.range' ((j + 1) * Str M n z T) (Str M n z T)).flatMap
      (ibits M n z T)) (layerBound M n z T) (fun j _ => by simp [lstart])
    (fun j hj => by
      have h := goes_layer M x (n := n) (z := z) hT (t := j + 1) (by omega) (T - j - 1) ps
      rw [lstart_succ] at h
      simp only [Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, if_false] at h
      refine h.congr ?_ rfl rfl rfl rfl le_rfl
      rw [ER.update_f]; congr 1)
  have hall := (s1.trans s2).trans s3
  refine hall.congr (by simp) (by simp) rfl rfl ?_ ?_
  · rw [range_mul, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [List.flatMap_assoc]
  · nlinarith

end UTab

end Complexity
