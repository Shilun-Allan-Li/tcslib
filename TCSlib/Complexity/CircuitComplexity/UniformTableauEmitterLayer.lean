/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterInstr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tableau emitter: one step of the tableau

The run of the emitter program `Complexity.UTab.prog` over one step `t` of the tableau: the
work cells of every tape (`Complexity.UTab.goes_cells`, `Complexity.UTab.goes_tapes`), the
input positions (`Complexity.UTab.goes_inputs`), and the snapshot
(`Complexity.UTab.goes_snap`); together (`Complexity.UTab.goes_layer`) they print the gate
bits of the instructions `tS, …, (t + 1)S − 1` of the uniform tableau circuit, `S` the
stride.

Throughout, the registers satisfy the step invariant: `n`, `|z|` and `T` in place, `I` the
current instruction, `Q = I − S` (or `0` at the first step), `LB = tS`, and the loop and
scratch registers at `0` between pieces.

## Main results

* `Complexity.UTab.goes_cells`, `Complexity.UTab.goes_tapes`, `Complexity.UTab.goes_inputs`,
  `Complexity.UTab.goes_snap`, `Complexity.UTab.goes_layer`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6; §6.2, Remark 6.7.)
-/

namespace Complexity

namespace UTab

open Turing BoolCircuit CounterProg

variable (M : FinTM Bool) (x : List Bool)

/-- The step bound of one instruction template. -/
noncomputable abbrev Ki : ℕ := Lmax M + 3

/-- **An instruction template at the step invariant**: it prints its micro-operations and
advances `I`, keeping `Q = I − S` (or `0` at the first step). -/
theorem goes_instr_inv (θ : Tpl M.k) (hθ : (θ.next : Lb M.k (Lmax M)) = .pI θ) {t S : ℕ}
    (ht0 : θ.t0 = decide (t = 0)) (e : ER) (hq : e.q = if t = 0 then 0 else e.i - S)
    (hS : t ≠ 0 → S ≤ e.i) (p : ℕ) :
    Goes (prog M) x (tpL θ) e.f p (some θ.after)
      { e with i := e.i + 1, q := if t = 0 then 0 else e.i + 1 - S }.f p
      ((tmpl M θ).flatMap (MOp.exec e.f)) (Ki M) := by
  refine (goes_instr M x θ hθ e p).congr rfl ?_ rfl rfl rfl
    (by have := length_tmpl_le M θ; simp only [Ki]; omega)
  rw [ht0]
  by_cases ht : t = 0
  · simp [ht] at hq ⊢; rw [hq]
  · have := hS ht
    simp [ht] at hq ⊢; rw [hq]; congr 2; omega

/-- A `range'` splits off its first element. -/
theorem range'_succ_left (s n : ℕ) : List.range' s (n + 1) = s :: List.range' (s + 1) n := by
  simp [List.range'_succ]

/-- A `range'` is a shifted `range`. -/
theorem range'_eq_map (s n : ℕ) : List.range' s n = (List.range n).map (s + ·) := by
  rw [List.range'_eq_map_range]

/-! ## The cells of one work tape -/

section Cells

variable {n : ℕ} {z : List Bool} {T t : ℕ}

/-- The stride of the uniform tableau of `M` with virtual input length `|z| + n`. -/
noncomputable abbrev Str (n : ℕ) (z : List Bool) (T : ℕ) : ℕ := cfgStride M (z.length + n) T

/-- The copy macro on records. -/
theorem goes_copyR (s : CpS M.k) (e : ER) (p : ℕ) (htmp : e.tmp = 0) :
    Goes (prog M) x (.cp s 0) e.f p (some s.exit) (e.set s.dst (e.f s.dst + e.f s.src)).f p
      [] (7 * e.f s.src + 2) := by
  rw [← ER.update_f]; exact goes_copy M x s e.f p (by simpa using htmp)

/-- The clear macro on records. -/
theorem goes_clearR (s : ClS) (e : ER) (p : ℕ) :
    Goes (prog M) x (.cl s 0 : Lb M.k (Lmax M)) e.f p (some s.exit) (e.set s.reg 0).f p
      [] (2 * e.f s.reg + 1) := by
  rw [← ER.update_f]; exact goes_clear M x s e.f p

/-- Splitting a `range'`. -/
theorem range'_add (s a b : ℕ) : List.range' s (a + b) = List.range' s a ++ List.range' (s +
    a) b := by
  have := List.range'_append (s := s) (m := a) (n := b) (step := 1)
  simp only [Nat.one_mul] at this; exact this.symm

/-- One cell instruction inside the cell loops, at the step invariant. -/
theorem goes_cell_one (τ : Fin M.k) (ph : Fin 5) {r : ℕ} (hr : r < 2 * T + 1) (ht : t ≤ T)
    (e : ER) (hn : e.nc = n) (hz : e.z = z.length)
    (hi : e.i = cellIdx M (z.length + n) T t τ r)
    (hq : e.q = if t = 0 then 0 else e.i - Str M n z T) (hlb : e.lb = t * Str M n z T)
    (h0 : decide (ph ≠ 0) = decide (1 ≤ r)) (h2 : decide (ph = 2) = decide (r = T))
    (h4 : decide (ph ≠ 4) = decide (r + 1 < 2 * T + 1)) (p : ℕ) :
    Goes (prog M) x (tpL (.cell τ (decide (t = 0)) ph)) e.f p
      (some (Tpl.cell τ (decide (t = 0)) ph).after)
      { e with i := e.i + 1, q := if t = 0 then 0 else e.i + 1 - Str M n z T }.f p
      (ibits M n z T e.i) (Ki M) := by
  have hS : t ≠ 0 → Str M n z T ≤ e.i := by
    intro h; rw [hi, cellIdx]
    have : 1 * Str M n z T ≤ t * Str M n z T := Nat.mul_le_mul_right _ (by omega)
    simp only [Str] at this ⊢; omega
  have h := goes_instr_inv M x (.cell τ (decide (t = 0)) ph) rfl rfl e hq hS p
  have hQ : t ≠ 0 → e.q + cfgStride M (z.length + n) T = e.i := fun h' => by
    have := hS h'; simp [h'] at hq; simp only [Str] at *; omega
  rwa [cell_bits M ph hr ht e hn hz hi hQ hlb h0 h2 h4] at h

/-- **The cells of one work tape**: from the cell `r = 0` of tape `τ` at step `t`, the
emitter prints the gate bits of the `2T + 1` cells and moves to the next tape.

**Proof sketch.** The cell `r = 0`; copy `T` into the loop counter and decrement it; the
loop over `r = 1, …, T − 1`; the origin `r = T`; again the counter and the loop over
`r = T + 1, …, 2T − 1`; the last cell `r = 2T` (`goes_cell_one` for each, with the flags of
its phase). -/
theorem goes_cells (τ : Fin M.k) (hT : 1 ≤ T) (ht : t ≤ T) (e : ER) (hn : e.nc = n)
    (hz : e.z = z.length) (heT : e.t = T) (hi : e.i = t * Str M n z T + τ * (2 * T + 1))
    (hq : e.q = if t = 0 then 0 else e.i - Str M n z T) (hlb : e.lb = t * Str M n z T)
    (hll : e.ll = 0) (htmp : e.tmp = 0) (p : ℕ) :
    Goes (prog M) x (tpL (.cell τ (decide (t = 0)) 0)) e.f p
      (some (cellStart (decide (t = 0)) (τ + 1)))
      { e with i := e.i + (2 * T + 1),
               q := if t = 0 then 0 else e.i + (2 * T + 1) - Str M n z T }.f p
      ((List.range' e.i (2 * T + 1)).flatMap (ibits M n z T)) ((2 * T + 3) * (Lmax M + 20)) := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  -- the state with `I = e.i + j` and loop counter `c`
  let st : ℕ → ℕ → ER := fun j c =>
    { e with i := e.i + j, q := if t = 0 then 0 else e.i + j - (Str M n z (T' + 1)), ll := c }
  have hcell : ∀ (ph : Fin 5) (j c : ℕ), j < 2 * (T' + 1) + 1 →
      decide (ph ≠ 0) = decide (1 ≤ j) → decide (ph = 2) = decide (j = T' + 1) →
      decide (ph ≠ 4) = decide (j + 1 < 2 * (T' + 1) + 1) →
      Goes (prog M) x (tpL (.cell τ (decide (t = 0)) ph)) (st j c).f p (some (Tpl.cell τ (decide (t
          = 0)) ph).after)
        (st (j + 1) c).f p (ibits M n z (T' + 1) (e.i + j)) (Ki M) := by
    intro ph j c hj h0 h2 h4
    have := goes_cell_one M x τ ph hj ht (st j c) hn hz (by simp only [st, hi, cellIdx, Str])
      (by simp [st]) hlb h0 h2 h4 p
    refine this.congr rfl ?_ rfl rfl (by simp [st]) le_rfl
    congr 1
  -- a loop over `T'` consecutive cells starting at `j₀`
  have hloop : ∀ (h : Hd M.k) (ph : Fin 5) (j₀ : ℕ), h.reg = rLL →
      (h.body : Lb M.k (Lmax M)) = tpL (.cell τ (decide (t = 0)) ph) →
      (Tpl.cell τ (decide (t = 0)) ph).after = (.hd h : Lb M.k (Lmax M)) →
      (∀ j < T', decide (ph ≠ 0) = decide (1 ≤ j₀ + j) ∧
        decide (ph = 2) = decide (j₀ + j = T' + 1) ∧
        decide (ph ≠ 4) = decide (j₀ + j + 1 < 2 * (T' + 1) + 1)) → j₀ + T' ≤ 2 * T' + 2 →
      Goes (prog M) x (.hd h) (st j₀ T').f p (some h.exit) (st (j₀ + T') 0).f p
        ((List.range' (e.i + j₀) T').flatMap (ibits M n z (T' + 1))) (T' * (Ki M + 2) + 1) := by
    intro h ph j₀ hreg hbody hafter hfl hle
    have := goes_loop (P := prog M) (x := x) (head := .hd h) (dl := .dl h) (body := h.body)
      (exit := h.exit) (r := rLL) (by simp [prog, hreg]) (by simp [prog, hreg]) T'
      (fun j => (st (j₀ + j) (T' - j)).f) (fun _ => p) (fun j => ibits M n z (T' + 1) (e.i + j₀ +
          j))
      (Ki M) (fun j _ => by simp [st]) (fun j hj => by
        rw [ER.update_f, hbody]
        obtain ⟨h0, h2, h4⟩ := hfl j hj
        have := hcell ph (j₀ + j) (T' - j - 1) (by omega) h0 h2 h4
        rw [hafter] at this
        refine this.congr ?_ ?_ rfl rfl (by ring_nf) le_rfl
        · congr 1
        · congr 1)
    refine this.congr (by simp) (by simp) rfl rfl ?_ le_rfl
    rw [range'_eq_map, List.flatMap_map]
  -- the pieces
  have e0 : e = st 0 0 := by ext <;> simp [st, hq, hll]
  have s1 := hcell 0 0 0 (by omega) (by decide) (by simp) (by simp)
  have s2 := goes_copyR M x (.cA τ (decide (t = 0))) (st 1 0) p (by simp [st, htmp])
  simp only [CpS.dst, CpS.src, ER.f_ll, ER.f_t, ER.set_ll, CpS.exit] at s2
  have s3 := goes_decR (P := prog M) (x := x) (l := .dA τ (decide (t = 0))) (l' := .hd (.cA τ
      (decide (t = 0))))
    (r := rLL) (e := { st 1 0 with ll := 0 + (st 1 0).t }) (p := p) rfl
  simp only [ER.f_ll, ER.set_ll] at s3
  have s4 := hloop (.cA τ (decide (t = 0))) 1 1 rfl rfl rfl (fun j hj => by
    refine ⟨by simp, ?_, by simp; omega⟩
    simp; omega) (by omega)
  have s5 := hcell 2 (1 + T') 0 (by omega) (by simp) (by simp; omega) (by simp; omega)
  have s6 := goes_copyR M x (.cB τ (decide (t = 0))) (st (1 + T' + 1) 0) p (by simp [st, htmp])
  simp only [CpS.dst, CpS.src, ER.f_ll, ER.f_t, ER.set_ll, CpS.exit] at s6
  have s7 := goes_decR (P := prog M) (x := x) (l := .dB τ (decide (t = 0))) (l' := .hd (.cB τ
      (decide (t = 0))))
    (r := rLL) (e := { st (1 + T' + 1) 0 with ll := 0 + (st (1 + T' + 1) 0).t }) (p := p) rfl
  simp only [ER.f_ll, ER.set_ll] at s7
  have s8 := hloop (.cB τ (decide (t = 0))) 3 (1 + T' + 1) rfl rfl rfl (fun j hj => by
    refine ⟨by simp; omega, ?_, by simp; omega⟩
    simp; omega) (by omega)
  have s9 := hcell 4 (1 + T' + 1 + T') 0 (by omega) (by simp; omega) (by simp; omega)
    (by simp; omega)
  have hst : ∀ j, { st j 0 with ll := 0 + (st j 0).t - 1 } = st j T' := by
    intro j; ext <;> simp [st, heT]
  rw [hst] at s3 s7
  have hall := (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans
    s8).trans s9
  rw [← e0] at hall
  refine hall.congr rfl ?_ rfl rfl ?_ ?_
  · congr 1
    ext <;> simp [st] <;> (try split_ifs) <;> omega
  · rw [show 2 * (T' + 1) + 1 = 1 + T' + 1 + T' + 1 by ring, range'_add, range'_add, range'_add,
      range'_add]
    simp [List.flatMap_append, Nat.add_assoc]
  · simp only [Ki, heT, st] at *
    nlinarith

/-- **The cells of all work tapes**: from the cells of tape `τ` on, the emitter prints the
gate bits of the cells of tapes `τ, …, k − 1` and reaches the input positions.

**Proof sketch.** Induction on the number of remaining tapes, `goes_cells` for each. -/
theorem goes_tapes (hT : 1 ≤ T) (ht : t ≤ T) : ∀ (d τ : ℕ) (e : ER), τ + d = M.k →
    e.nc = n → e.z = z.length → e.t = T → e.i = t * Str M n z T + τ * (2 * T + 1) →
    e.q = (if t = 0 then 0 else e.i - Str M n z T) → e.lb = t * Str M n z T → e.ll = 0 →
    e.tmp = 0 → ∀ p : ℕ,
    Goes (prog M) x (cellStart (decide (t = 0)) τ) e.f p (some (tpL (.inp (decide (t = 0)) .p0)))
      { e with i := e.i + d * (2 * T + 1),
               q := if t = 0 then 0 else e.i + d * (2 * T + 1) - Str M n z T }.f p
      ((List.range' e.i (d * (2 * T + 1))).flatMap (ibits M n z T))
      (d * ((2 * T + 3) * (Lmax M + 20))) := by
  intro d
  induction d with
  | zero =>
    intro τ e hτ hn hz heT hi hq hlb hll htmp p
    have : ¬ τ < M.k := by omega
    simp only [cellStart, this, dite_false, Nat.zero_mul, Nat.add_zero, List.range'_zero,
      List.flatMap_nil]
    refine (goes_refl _ _ _).congr rfl ?_ rfl rfl rfl le_rfl
    congr 1; ext <;> simp [hq]
  | succ d ih =>
    intro τ e hτ hn hz heT hi hq hlb hll htmp p
    have hlt : τ < M.k := by omega
    have h1 := goes_cells M x ⟨τ, hlt⟩ hT ht e hn hz heT hi hq hlb hll htmp p
    have h2 := ih (τ + 1) { e with i := e.i + (2 * T + 1),
                                   q := if t = 0 then 0 else e.i + (2 * T + 1) - Str M n z T }
      (by omega) hn hz heT (by simp [hi]; ring) rfl hlb hll htmp p
    simp only [cellStart, hlt, dite_true]
    refine (h1.trans h2).congr rfl ?_ rfl rfl ?_ (by ring_nf; omega)
    · congr 1; ext <;> simp <;> (try split_ifs) <;> ring_nf
    · rw [show (d + 1) * (2 * T + 1) = (2 * T + 1) + d * (2 * T + 1) by ring,
        range'_add e.i (2 * T + 1) (d * (2 * T + 1)), List.flatMap_append]

end Cells

/-! ## The input positions -/

section Inputs

variable {n : ℕ} {z : List Bool} {T t : ℕ}

/-- The layout reads position `k` of the virtual input. -/
theorem tabLayout_getD {N k : ℕ} (hk : k < N) : (tabLayout N).getD k (.const false) = .input k := by
  unfold tabLayout; rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp

/-- The layout reads position `k` of the virtual input. -/
theorem getElem?_tabLayout {N k : ℕ} (hk : k < N) : (tabLayout N)[k]? = some (.input k) := by
  simp [tabLayout, hk]

/-- One input-position instruction at the step invariant. -/
theorem goes_inp_one (ph : IPh) {p : ℕ} (hp : p < z.length + n + 2) (ht : t ≤ T) (e : ER)
    (hn : e.nc = n) (hz : e.z = z.length) (hi : e.i = inpIdx M (z.length + n) T t p)
    (hq : e.q = if t = 0 then 0 else e.i - Str M n z T) (hlb : e.lb = t * Str M n z T)
    (hph : inpPhS (k := M.k) (snapWidth M) (decide (t = 0)) ph =
      inpS (snapWidth M) (decide (t = 0)) (decide (p = 0)) (decide (p = 1))
        (decide (p = z.length + n + 1)) ph.lay)
    (hlay : (layS (k := M.k) ph.lay).toBitSrc e.f = if 1 ≤ p ∧ p ≤ z.length + n then
        (tabLayout (z.length + n)).getD (p - 1) (.const false) else .const false)
    (hlayok : (layS (k := M.k) ph.lay).Ok e.f) (ps : ℕ) :
    Goes (prog M) x (tpL (.inp (decide (t = 0)) ph)) e.f ps
      (some (Tpl.inp (decide (t = 0)) ph).after)
      { e with i := e.i + 1, q := if t = 0 then 0 else e.i + 1 - Str M n z T }.f ps
      (ibits M n z T e.i) (Ki M) := by
  have hS : t ≠ 0 → Str M n z T ≤ e.i := by
    intro h; rw [hi, inpIdx]
    have : 1 * Str M n z T ≤ t * Str M n z T := Nat.mul_le_mul_right _ (by omega)
    simp only [Str] at this ⊢; omega
  have h := goes_instr_inv M x (.inp (decide (t = 0)) ph) rfl rfl e hq hS ps
  rwa [inp_bits M ph hp ht e hn hz hi (fun h' => by
    have := hS h'; simp [h'] at hq; simp only [Str] at *; omega) hlb hph hlay hlayok] at h

/-- **The input positions of one step**: from position `0`, the emitter prints the gate bits
of the `N + 2` input positions (`N = |z| + n`) and reaches the snapshot.

**Proof sketch.** Position `0`; copy `|z|` into the loop counter and loop over the hard-wired
positions (the first one, `p = 1`, recognised by `PA = 0`); copy `n` and loop over the free
positions (`p = 1` iff `PB = 0` and `|z| = 0`); the right end (`p = 1` iff `|z| = n = 0`);
clear the position counters. -/
theorem goes_inputs (ht : t ≤ T) (e : ER) (hn : e.nc = n) (hz : e.z = z.length)
    (hi : e.i = t * Str M n z T + M.k * (2 * T + 1))
    (hq : e.q = if t = 0 then 0 else e.i - Str M n z T) (hlb : e.lb = t * Str M n z T)
    (hll : e.ll = 0) (hpa : e.pa = 0) (hpb : e.pb = 0) (htmp : e.tmp = 0) (ps : ℕ) :
    Goes (prog M) x (tpL (.inp (decide (t = 0)) .p0)) e.f ps (some (tpL (.snap (decide (t = 0)))))
      { e with i := e.i + (z.length + n + 2),
               q := if t = 0 then 0 else e.i + (z.length + n + 2) - Str M n z T }.f ps
      ((List.range' e.i (z.length + n + 2)).flatMap (ibits M n z T))
      ((z.length + n + 2) * (Lmax M + 20)) := by
  -- the state at position `p` with counters
  let st : ℕ → ℕ → ℕ → ℕ → ER := fun p a b c =>
    { e with i := e.i + p, q := if t = 0 then 0 else e.i + p - Str M n z T, pa := a, pb := b,
             ll := c }
  have hinp : ∀ (ph : IPh) (p a b c : ℕ), p < z.length + n + 2 →
      inpPhS (k := M.k) (snapWidth M) (decide (t = 0)) ph =
        inpS (snapWidth M) (decide (t = 0)) (decide (p = 0)) (decide (p = 1))
          (decide (p = z.length + n + 1)) ph.lay →
      (layS (k := M.k) ph.lay).toBitSrc (st p a b c).f = (if 1 ≤ p ∧ p ≤ z.length + n then
        (tabLayout (z.length + n)).getD (p - 1) (.const false) else .const false) →
      (layS (k := M.k) ph.lay).Ok (st p a b c).f →
      Goes (prog M) x (tpL (.inp (decide (t = 0)) ph)) (st p a b c).f ps
        (some (Tpl.inp (decide (t = 0)) ph).after) (st (p + 1) a b c).f ps
        (ibits M n z T (e.i + p)) (Ki M) := by
    intro ph p a b c hp hph hlay hlayok
    have := goes_inp_one M x ph hp ht (st p a b c) hn hz (by simp only [st, hi, inpIdx, Str])
      (by simp [st]) hlb hph hlay hlayok ps
    exact this.congr rfl (by congr 1) rfl rfl (by simp [st]) le_rfl
  have e0 : e = st 0 0 0 0 := by ext <;> simp [st, hq, hll, hpa, hpb]
  -- position 0
  have s1 := hinp .p0 0 0 0 0 (by omega) (by simp [inpPhS, IPh.lay])
    (by simp [layS, SSrc.toBitSrc, IPh.lay]) trivial
  -- the hard-wired positions
  have s2 := goes_copyR M x (.iz (decide (t = 0))) (st 1 0 0 0) ps (by simp [st, htmp])
  simp only [CpS.dst, CpS.src, ER.f_ll, ER.f_z, ER.set_ll, CpS.exit] at s2
  have hz1 : { st 1 0 0 0 with ll := 0 + (st 1 0 0 0).z } = st 1 0 0 z.length := by
    ext <;> simp [st, hz]
  rw [hz1] at s2
  have s3 := goes_loop (P := prog M) (x := x) (head := .hd (.iz (decide (t = 0))))
    (dl := .dl (.iz (decide (t = 0)))) (body := .zb (decide (t = 0)))
    (exit := .cp (.iu (decide (t = 0))) 0) (r := rLL) (by simp [prog, Hd.reg, Hd.exit])
    (by simp [prog, Hd.reg, Hd.body]) z.length (fun j => (st (1 + j) j 0 (z.length - j)).f)
    (fun _ => ps) (fun j => ibits M n z T (e.i + 1 + j)) (Ki M + 2) (fun j _ => by simp [st])
    (fun j hj => by
      rw [ER.update_f]
      have hb : ∀ ph : IPh, (ph = .zA ∨ ph = .zB) → (decide (j = 0) ↔ ph = .zA) →
          Goes (prog M) x (tpL (.inp (decide (t = 0)) ph))
            ((st (1 + j) j 0 (z.length - j)).set rLL (z.length - j - 1)).f ps
            (some (.hd (.iz (decide (t = 0))))) (st (1 + (j + 1)) (j + 1) 0 (z.length - (j +
                1))).f ps
            (ibits M n z T (e.i + 1 + j)) (Ki M + 1) := by
        intro ph hph hph'
        have h1 := hinp ph (1 + j) j 0 (z.length - j - 1) (by omega)
          (by
            rcases hph with rfl | rfl
            · have : j = 0 := by simpa using hph'
              subst this; simp only [inpPhS, IPh.lay]; congr 1; simp; intro h; simp [h] at hj
            · have : j ≠ 0 := by simpa using hph'
              simp only [inpPhS, IPh.lay]; congr 1 <;> simp <;> omega)
          (by
            rcases hph with rfl | rfl <;>
              simp [layS, SSrc.toBitSrc, IPh.lay, st, show 1 ≤ 1 + j by omega,
                show 1 + j ≤ z.length + n by omega,
                getElem?_tabLayout (show j < z.length + n by omega)])
          (by rcases hph with rfl | rfl <;> simp [layS, SSrc.Ok, IPh.lay, st, hz] <;> omega)
        have h2 := goes_incR (P := prog M) (x := x) (l := .iPA (decide (t = 0)))
          (l' := .hd (.iz (decide (t = 0)))) (r := rPA) (e := st (1 + j + 1) j 0 (z.length - j - 1))
          (p := ps) rfl
        have hafter : (Tpl.inp (decide (t = 0)) ph).after = (.iPA (decide (t = 0)) : Lb M.k (Lmax
            M)) := by
          rcases hph with rfl | rfl <;> rfl
        rw [hafter] at h1
        refine (h1.trans h2).congr ?_ ?_ rfl rfl (by simp [Nat.add_assoc]) le_rfl
        · congr 1
        · congr 1
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        refine ((goes_jz_zero (P := prog M) (x := x) (p := ps) (l := .zb (decide (t = 0)))
          (r := rPA) rfl (by simp [st])).trans (hb .zA (Or.inl rfl) (by simp))).mono
          (by omega)
      · refine ((goes_jz_pos (P := prog M) (x := x) (p := ps) (l := .zb (decide (t = 0)))
          (r := rPA) rfl (by simp [st]; omega)).trans
            (hb .zB (Or.inr rfl) (by simp; omega))).mono (by omega))
  simp only [Nat.add_zero, Nat.sub_zero, Nat.sub_self] at s3
  -- the free positions
  have s4 := goes_copyR M x (.iu (decide (t = 0))) (st (1 + z.length) z.length 0 0) ps
    (by simp [st, htmp])
  simp only [CpS.dst, CpS.src, ER.f_ll, ER.f_nc, ER.set_ll, CpS.exit] at s4
  have hn1 : { st (1 + z.length) z.length 0 0 with ll := 0 + (st (1 + z.length) z.length 0 0).nc } =
      st (1 + z.length) z.length 0 n := by
    ext <;> simp [st, hn]
  rw [hn1] at s4
  have s5 := goes_loop (P := prog M) (x := x) (head := .hd (.iu (decide (t = 0))))
    (dl := .dl (.iu (decide (t = 0)))) (body := .ub (decide (t = 0)))
    (exit := .eT (decide (t = 0))) (r := rLL) (by simp [prog, Hd.reg, Hd.exit])
    (by simp [prog, Hd.reg, Hd.body]) n (fun j => (st (1 + z.length + j) z.length j (n - j)).f)
    (fun _ => ps) (fun j => ibits M n z T (e.i + (1 + z.length) + j)) (Ki M + 3)
    (fun j _ => by simp [st])
    (fun j hj => by
      rw [ER.update_f]
      have hb : ∀ ph : IPh, (ph = .uA ∨ ph = .uB) → (ph = .uA ↔ (j = 0 ∧ z.length = 0)) →
          Goes (prog M) x (tpL (.inp (decide (t = 0)) ph))
            ((st (1 + z.length + j) z.length j (n - j)).set rLL (n - j - 1)).f ps
            (some (.hd (.iu (decide (t = 0)))))
            (st (1 + z.length + (j + 1)) z.length (j + 1) (n - (j + 1))).f ps
            (ibits M n z T (e.i + (1 + z.length) + j)) (Ki M + 1) := by
        intro ph hph hph'
        have h1 := hinp ph (1 + z.length + j) z.length j (n - j - 1) (by omega)
          (by
            rcases hph with rfl | rfl
            · have : j = 0 ∧ z.length = 0 := hph'.mp rfl
              simp only [inpPhS, IPh.lay]; congr 1 <;> simp <;> omega
            · have : ¬ (j = 0 ∧ z.length = 0) := fun h => absurd (hph'.mpr h) (by decide)
              simp only [inpPhS, IPh.lay]; congr 1 <;> simp <;> omega)
          (by
            rcases hph with rfl | rfl <;>
              simp [layS, SSrc.toBitSrc, IPh.lay, st, hz, show 1 ≤ 1 + z.length + j by omega,
                show 1 + z.length + j ≤ z.length + n by omega,
                show 1 + z.length + j - 1 = z.length + j by omega, getElem?_tabLayout (show
                    z.length + j < z.length + n by omega)])
          (by rcases hph with rfl | rfl <;> trivial)
        have h2 := goes_incR (P := prog M) (x := x) (l := .iPB (decide (t = 0)))
          (l' := .hd (.iu (decide (t = 0)))) (r := rPB)
          (e := st (1 + z.length + j + 1) z.length j (n - j - 1)) (p := ps) rfl
        have hafter : (Tpl.inp (decide (t = 0)) ph).after =
            (.iPB (decide (t = 0)) : Lb M.k (Lmax M)) := by
          rcases hph with rfl | rfl <;> rfl
        rw [hafter] at h1
        refine (h1.trans h2).congr ?_ ?_ rfl rfl (by simp [Nat.add_assoc]) le_rfl
        · congr 1
        · congr 1
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        have hj1 := goes_jz_zero (P := prog M) (x := x) (p := ps) (l := .ub (decide (t = 0)))
          (r := rPB) (ρ := ((st (1 + z.length + 0) z.length 0 (n - 0)).set rLL (n - 0 - 1)).f)
          rfl (by simp [st])
        rcases Nat.eq_zero_or_pos z.length with hz0 | hz0
        · have hj2 := goes_jz_zero (P := prog M) (x := x) (p := ps) (l := .ub2 (decide (t = 0)))
            (r := rZ) (ρ := ((st (1 + z.length + 0) z.length 0 (n - 0)).set rLL (n - 0 - 1)).f)
            rfl (by simp only [st, ER.set_ll, ER.f_z, hz, hz0])
          exact ((hj1.trans hj2).trans (hb .uA (Or.inl rfl) ⟨fun _ => ⟨rfl, hz0⟩, fun _ =>
              rfl⟩)).mono
            (by omega)
        · have hj2 := goes_jz_pos (P := prog M) (x := x) (p := ps) (l := .ub2 (decide (t = 0)))
            (r := rZ) (ρ := ((st (1 + z.length + 0) z.length 0 (n - 0)).set rLL (n - 0 - 1)).f)
            rfl (by simp only [st, ER.set_ll, ER.f_z, hz]; omega)
          exact ((hj1.trans hj2).trans (hb .uB (Or.inr rfl)
            ⟨fun h => absurd h (by decide), fun h => absurd h.2 (by omega)⟩)).mono (by omega)
      · exact ((goes_jz_pos (P := prog M) (x := x) (p := ps) (l := .ub (decide (t = 0)))
          (r := rPB) rfl (by simp only [st, ER.set_ll, ER.f_pb]; omega)).trans
            (hb .uB (Or.inr rfl) ⟨fun h => absurd h (by decide), fun h => absurd h.1 (by
                omega)⟩)).mono
              (by omega))
  simp only [Nat.add_zero, Nat.sub_zero, Nat.sub_self] at s5
  -- the right end
  have hend : ∀ ph : IPh, (ph = .e1 ∨ ph = .e2) → (ph = .e1 ↔ (z.length = 0 ∧ n = 0)) →
      Goes (prog M) x (tpL (.inp (decide (t = 0)) ph)) (st (1 + z.length + n) z.length n 0).f ps
        (some (.cl (.pa (decide (t = 0))) 0)) (st (1 + z.length + n + 1) z.length n 0).f ps
        (ibits M n z T (e.i + (1 + z.length + n))) (Ki M) := by
    intro ph hph hph'
    have h1 := hinp ph (1 + z.length + n) z.length n 0 (by omega)
      (by
        rcases hph with rfl | rfl
        · have : z.length = 0 ∧ n = 0 := hph'.mp rfl
          simp only [inpPhS, IPh.lay]; congr 1 <;> simp <;> omega
        · have : ¬ (z.length = 0 ∧ n = 0) := fun h => absurd (hph'.mpr h) (by decide)
          simp only [inpPhS, IPh.lay]; congr 1 <;> simp <;> omega)
      (by rcases hph with rfl | rfl <;> simp [layS, SSrc.toBitSrc, IPh.lay])
      (by rcases hph with rfl | rfl <;> trivial)
    have hafter : (Tpl.inp (decide (t = 0)) ph).after =
        (.cl (.pa (decide (t = 0))) 0 : Lb M.k (Lmax M)) := by
      rcases hph with rfl | rfl <;> rfl
    rwa [hafter] at h1
  have s6 : Goes (prog M) x (.eT (decide (t = 0))) (st (1 + z.length + n) z.length n 0).f ps
      (some (.cl (.pa (decide (t = 0))) 0)) (st (1 + z.length + n + 1) z.length n 0).f ps
      (ibits M n z T (e.i + (1 + z.length + n))) (Ki M + 2) := by
    rcases Nat.eq_zero_or_pos z.length with hz0 | hz0
    · have hj1 := goes_jz_zero (P := prog M) (x := x) (p := ps) (l := .eT (decide (t = 0)))
        (r := rZ) (ρ := (st (1 + z.length + n) z.length n 0).f) rfl
        (by simp only [st, ER.f_z, hz, hz0])
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · have hj2 := goes_jz_zero (P := prog M) (x := x) (p := ps) (l := .eT2 (decide (t = 0)))
          (r := rNC) (ρ := (st (1 + z.length + n) z.length n 0).f) rfl
          (by simp only [st, ER.f_nc, hn, hn0])
        exact ((hj1.trans hj2).trans (hend .e1 (Or.inl rfl) ⟨fun _ => ⟨hz0, hn0⟩, fun _ =>
            rfl⟩)).mono
          (by omega)
      · have hj2 := goes_jz_pos (P := prog M) (x := x) (p := ps) (l := .eT2 (decide (t = 0)))
          (r := rNC) (ρ := (st (1 + z.length + n) z.length n 0).f) rfl
          (by simp only [st, ER.f_nc, hn]; omega)
        exact ((hj1.trans hj2).trans (hend .e2 (Or.inr rfl)
          ⟨fun h => absurd h (by decide), fun h => absurd h.2 (by omega)⟩)).mono (by omega)
    · exact ((goes_jz_pos (P := prog M) (x := x) (p := ps) (l := .eT (decide (t = 0)))
        (r := rZ) (ρ := (st (1 + z.length + n) z.length n 0).f) rfl
        (by simp only [st, ER.f_z, hz]; omega)).trans
          (hend .e2 (Or.inr rfl) ⟨fun h => absurd h (by decide), fun h => absurd h.1 (by
              omega)⟩)).mono
            (by omega)
  -- clearing the position counters
  have s7 := goes_clearR M x (.pa (decide (t = 0))) (st (1 + z.length + n + 1) z.length n 0) ps
  simp only [ClS.reg, ClS.exit, ER.f_pa, ER.set_pa] at s7
  have s8 := goes_clearR M x (.pb (decide (t = 0)))
    { st (1 + z.length + n + 1) z.length n 0 with pa := 0 } ps
  simp only [ClS.reg, ClS.exit, ER.f_pb, ER.set_pb] at s8
  have hall := (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8)
  rw [← e0] at hall
  refine hall.congr rfl ?_ rfl rfl ?_ ?_
  · congr 1; ext <;> simp [st] <;> (try split_ifs) <;> omega
  · rw [show z.length + n + 2 = 1 + z.length + n + 1 by omega, range'_add, range'_add, range'_add]
    simp [List.flatMap_append, range'_eq_map, List.flatMap_map, Nat.add_assoc]
  · simp only [Ki, st] at *
    nlinarith

end Inputs

end UTab

end Complexity
