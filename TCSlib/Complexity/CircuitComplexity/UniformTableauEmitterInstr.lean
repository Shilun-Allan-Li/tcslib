/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitter

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tableau emitter: templates and macros

Run lemmas for the pieces of the emitter program `Complexity.UTab.prog`: a template prints
its micro-operations (`Complexity.UTab.goes_tp`), an instruction template also advances the
instruction counters (`Complexity.UTab.goes_instr`), and the copy and clear macros
(`Complexity.UTab.goes_copy`, `Complexity.UTab.goes_clear`).  The second half proves that
the template of a tableau instruction prints exactly the gates of that instruction in the
uniform tableau circuit (`Complexity.UTab.instr_bits`), given that the registers point at
it.

## Main results

* `Complexity.UTab.goes_tp`, `Complexity.UTab.goes_instr`, `Complexity.UTab.goes_copy`,
  `Complexity.UTab.goes_clear`.
* `Complexity.UTab.instr_bits` — an instruction template prints the gates
  `BoolCircuit.tabInstrGates` of its instruction.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.2, Remark 6.7.)
-/

namespace Complexity

namespace UTab

open Turing BoolCircuit CounterProg

variable (M : FinTM Bool) (x : List Bool)

/-- Setting register `NC` of a record. -/
@[simp] theorem ER.set_nc (e : ER) (v : ℕ) : e.set rNC v = { e with nc := v } := rfl
/-- Setting register `Z` of a record. -/
@[simp] theorem ER.set_z (e : ER) (v : ℕ) : e.set rZ v = { e with z := v } := rfl
/-- Setting register `T` of a record. -/
@[simp] theorem ER.set_t (e : ER) (v : ℕ) : e.set rT v = { e with t := v } := rfl
/-- Setting register `I` of a record. -/
@[simp] theorem ER.set_i (e : ER) (v : ℕ) : e.set rI v = { e with i := v } := rfl
/-- Setting register `Q` of a record. -/
@[simp] theorem ER.set_q (e : ER) (v : ℕ) : e.set rQ v = { e with q := v } := rfl
/-- Setting register `LB` of a record. -/
@[simp] theorem ER.set_lb (e : ER) (v : ℕ) : e.set rLB v = { e with lb := v } := rfl
/-- Setting register `LT` of a record. -/
@[simp] theorem ER.set_lt (e : ER) (v : ℕ) : e.set rLT v = { e with lt := v } := rfl
/-- Setting register `LL` of a record. -/
@[simp] theorem ER.set_ll (e : ER) (v : ℕ) : e.set rLL v = { e with ll := v } := rfl
/-- Setting register `PA` of a record. -/
@[simp] theorem ER.set_pa (e : ER) (v : ℕ) : e.set rPA v = { e with pa := v } := rfl
/-- Setting register `PB` of a record. -/
@[simp] theorem ER.set_pb (e : ER) (v : ℕ) : e.set rPB v = { e with pb := v } := rfl
/-- Setting register `TMP` of a record. -/
@[simp] theorem ER.set_tmp (e : ER) (v : ℕ) : e.set rTMP v = { e with tmp := v } := rfl

/-! ## Templates and instructions -/

/-- **Running a template** prints its micro-operations and continues at its successor. -/
theorem goes_tp (θ : Tpl M.k) (ρ : Fin 11 → ℕ) (p : ℕ) :
    Goes (prog M) x (tpL θ) ρ p (some θ.next) ρ p ((tmpl M θ).flatMap (MOp.exec ρ))
      ((tmpl M θ).length + 1) := by
  have hle := length_tmpl_le M θ
  have := goes_tmpl (P := prog M) (x := x) (tmpl M θ)
    (fun i => (.tp θ (Fin.ofNat _ i) : Lb M.k (Lmax M))) θ.next (fun i hi => by
      simp only [prog]
      congr 1
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by omega)) ρ p
  simpa [tpL] using this

/-- **An instruction template** prints its micro-operations, then advances `I` (and `Q`
after the first step). -/
theorem goes_instr (θ : Tpl M.k) (hθ : (θ.next : Lb M.k (Lmax M)) = .pI θ) (e : ER) (p : ℕ) :
    Goes (prog M) x (tpL θ) e.f p (some θ.after)
      (if θ.t0 then { e with i := e.i + 1 } else { e with i := e.i + 1, q := e.q + 1 }).f p
      ((tmpl M θ).flatMap (MOp.exec e.f)) ((tmpl M θ).length + 3) := by
  have h1 := goes_tp M x θ e.f p
  rw [hθ] at h1
  have h2 := goes_incR (P := prog M) (x := x) (e := e) (p := p) (l := .pI θ) (l' := .pQ θ)
    (r := rI) rfl
  simp only [ER.f_i, ER.set_i] at h2
  cases ht : θ.t0
  · have h3 := goes_incR (P := prog M) (x := x) (e := { e with i := e.i + 1 }) (p := p)
      (l := .pQ θ) (l' := θ.after) (r := rQ) (by simp [prog, ht])
    simp only [ER.f_q, ER.set_q] at h3
    simpa using (h1.trans h2).trans h3
  · have h3 := goes_goto (P := prog M) (x := x) (ρ := ({ e with i := e.i + 1 } : ER).f) (p := p)
      (l := .pQ θ) (l' := θ.after) (by simp [prog, ht])
    simpa using ((h1.trans h2).trans h3).mono (by omega)

/-! ## Macros -/

/-- The three registers of a copy site are distinct. -/
theorem CpS.regs_ne (s : CpS M.k) : s.src ≠ s.dst ∧ s.src ≠ rTMP ∧ s.dst ≠ rTMP := by
  cases s <;> simp only [CpS.src, CpS.dst] <;> decide

/-- **The copy macro** adds the source register to the destination (scratch `0`, source and
scratch restored), within `7 v + 2` steps for a source of value `v`.

**Proof sketch.** Two count-down loops (`goes_loop`): the first moves the source into both
the destination and the scratch, the second moves the scratch back into the source. -/
theorem goes_copy (s : CpS M.k) (ρ : Fin 11 → ℕ) (p : ℕ) (htmp : ρ rTMP = 0) :
    Goes (prog M) x (.cp s 0) ρ p (some s.exit) (Function.update ρ s.dst (ρ s.dst + ρ s.src)) p
      [] (7 * ρ s.src + 2) := by
  obtain ⟨h1, h2, h3⟩ := CpS.regs_ne M s
  set v := ρ s.src with hv
  set d := ρ s.dst with hd
  -- the first loop: move the source into the destination and the scratch
  let st : ℕ → Fin 11 → ℕ := fun j =>
    Function.update (Function.update (Function.update ρ s.src (v - j)) s.dst (d + j)) rTMP j
  have hst0 : st 0 = ρ := by
    funext r; simp only [st, Function.update_apply]; split_ifs <;> subst_vars <;> simp_all
  have loop1 := goes_loop (P := prog M) (x := x) (head := .cp s 0) (dl := .cp s 1)
    (body := .cp s 2) (exit := .cp s 3) (r := s.src) (by simp [prog]) (by simp [prog]) v st
    (fun _ => p) (fun _ => []) 2 (fun j _ => by simp [st, h1, h2])
    (fun j hj => by
      have a := goes_inc (P := prog M) (x := x) (l := .cp s 2) (l' := .cp s 6) (r := s.dst)
        (ρ := Function.update (st j) s.src (v - j - 1)) (p := p) (by simp [prog])
      have b := goes_inc (P := prog M) (x := x) (l := .cp s 6) (l' := .cp s 0) (r := rTMP)
        (ρ := Function.update (Function.update (st j) s.src (v - j - 1)) s.dst
          (Function.update (st j) s.src (v - j - 1) s.dst + 1)) (p := p)
        (by simp [prog])
      refine (a.trans b).congr rfl ?_ rfl rfl rfl le_rfl
      funext r
      simp only [st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [hst0] at loop1
  -- the second loop: move the scratch back into the source
  let st' : ℕ → Fin 11 → ℕ := fun j =>
    Function.update (Function.update (Function.update ρ s.src j) s.dst (d + v)) rTMP (v - j)
  have hst' : st v = st' 0 := by
    funext r; simp only [st, st', Function.update_apply]; split_ifs <;> simp_all
  have loop2 := goes_loop (P := prog M) (x := x) (head := .cp s 3) (dl := .cp s 4)
    (body := .cp s 5) (exit := s.exit) (r := rTMP) (by simp [prog]) (by simp [prog]) v st'
    (fun _ => p) (fun _ => []) 1 (fun j _ => by simp [st']) (fun j hj => by
      have a := goes_inc (P := prog M) (x := x) (l := .cp s 5) (l' := .cp s 3) (r := s.src)
        (ρ := Function.update (st' j) rTMP (v - j - 1)) (p := p) (by simp [prog])
      refine (a.mono (by omega)).congr rfl ?_ rfl rfl rfl le_rfl
      funext r
      simp only [st', Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
      omega)
  have hend : st' v = Function.update ρ s.dst (d + v) := by
    funext r; simp only [st', Function.update_apply]; split_ifs <;> subst_vars <;> simp_all
  rw [← hst', hend] at loop2
  refine (loop1.trans loop2).congr rfl rfl rfl rfl (by simp) (by nlinarith)

/-- **The clear macro** sets a register to `0` within `2 v + 1` steps. -/
theorem goes_clear (s : ClS) (ρ : Fin 11 → ℕ) (p : ℕ) :
    Goes (prog M) x (.cl s 0 : Lb M.k (Lmax M)) ρ p (some s.exit) (Function.update ρ s.reg 0) p
      [] (2 * ρ s.reg + 1) := by
  let st : ℕ → Fin 11 → ℕ := fun j => Function.update ρ s.reg (ρ s.reg - j)
  have h := goes_loop (P := prog M) (x := x) (head := .cl s 0) (dl := .cl s 1)
    (body := .cl s 0) (exit := s.exit) (r := s.reg) (by simp [prog]) (by simp [prog])
    (ρ s.reg) st (fun _ => p) (fun _ => []) 0 (fun j _ => by simp [st]) (fun j hj => by
      refine (goes_refl _ _ _).congr rfl ?_ rfl rfl rfl le_rfl
      funext r; simp only [st, Function.update_apply]; split_ifs <;> omega)
  have h0 : st 0 = ρ := by
    funext r; simp only [st, Nat.sub_zero, Function.update_apply]; split_ifs with h <;> simp [h]
  rw [h0] at h
  exact h.congr rfl (by simp [st]) rfl rfl (by simp) (by omega)

/-! ## What an instruction template prints -/

/-- The gate bits of a list of mapped gates. -/
theorem gbits_map {α : Type} (l : List α) (f : α → DAGGate) :
    gbits (l.map f) = l.flatMap fun a => true :: (f a).encode := by
  simp [gbits, List.flatMap_map]

/-- An instruction template prints a copy gate per symbolic source and its kind's fixed part
shifted to the base. -/
theorem instrOps_exec (θ : Tpl M.k) (ρ : Fin 11 → ℕ) :
    (instrOps M θ).flatMap (MOp.exec ρ) =
      gbits ((θ.srcs (snapWidth M) (cfgArity M)).map fun s => copyGate ((s.toLinE M).val ρ)) ++
      gbits ((tabFixed (cfgArity M) (cfgWidth M) (cfgF M) θ.kind).map
        (shiftGate ((baseE M).val ρ))) := by
  rw [instrOps, List.flatMap_append, gbits_map, gbits_map, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  · apply List.flatMap_congr; intro s _
    rw [flatMap_exec_sgOps]; rfl
  · apply List.flatMap_congr; intro g _
    rw [flatMap_exec_sgOps]
    simp only [List.map_map, shiftGate]
    congr 3
    apply List.map_congr_left; intro a _
    simp [LinE.val]; omega

/-- The base expression prints the base of the current instruction. -/
theorem baseE_val {n : ℕ} {z : List Bool} (e : ER) (hn : e.nc = n) (hz : e.z = z.length) :
    (baseE M).val e.f = tabBase (cfgArity M) (cfgWidth M) (cfgF M) n z e.i := by
  simp only [baseE, LinE.val, List.map_cons, List.map_replicate, List.sum_cons,
    List.sum_replicate_nat, ER.f_nc, ER.f_z, ER.f_i, tabBase, hn, hz]
  ring

/-- **An instruction template prints its instruction's gates**: if the symbolic sources
denote the instruction's sources (and satisfy their side conditions), the kinds agree, and
the registers hold `n`, `|z|` and the instruction index, the template prints
`BoolCircuit.tabInstrGates` of the instruction in the uniform tableau circuit.

**Proof sketch.** The copy gates print the vertices of the sources
(`Complexity.UTab.tabSrc_toBitSrc`), the fixed part is printed relative to the base
(`baseE_val`). -/
theorem instr_bits {n : ℕ} {z : List Bool} (θ : Tpl M.k) (hθ : tmpl M θ = instrOps M θ)
    (e : ER) (hn : e.nc = n) (hz : e.z = z.length) (ins : GInstr (CfgKind M.k))
    (hk : ins.kind = θ.kind)
    (hs : (θ.srcs (snapWidth M) (cfgArity M)).map (SSrc.toBitSrc e.f) = ins.srcs)
    (hm : ins.srcs.length = cfgArity M)
    (hok : ∀ s ∈ θ.srcs (snapWidth M) (cfgArity M), s.Ok e.f)
    (hv : ∀ s ∈ ins.srcs, s.Valid (z.length + n) (cfgWidth M) e.i) :
    (tmpl M θ).flatMap (MOp.exec e.f) =
      gbits (tabInstrGates (cfgArity M) (cfgWidth M) (cfgF M) n z e.i ins) := by
  rw [hθ, instrOps_exec, tabInstrGates, gbits_append, hk, baseE_val M e hn hz]
  congr 2
  rw [padSrc, List.take_left' hm, ← hs, List.map_map]
  apply List.map_congr_left
  intro s hsm
  simp only [Function.comp]
  rw [tabSrc_toBitSrc M (by simpa using hn) (by simpa using hz) s (hok s hsm)
    (hv _ (hs ▸ List.mem_map_of_mem hsm))]

/-! ## The side conditions of the tableau templates -/

/-- Constants and padding satisfy every side condition. -/
theorem ok_padS {ρ : Fin 11 → ℕ} {m : ℕ} {l : List (SSrc M.k)} (h : ∀ s ∈ l, s.Ok ρ) :
    ∀ s ∈ padS m l, s.Ok ρ := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h s hs
  · rw [(List.mem_replicate.mp hs).2]; trivial

/-- A neighbour source satisfies its side condition when `Q + d ≥ 1` whenever it is used. -/
theorem ok_nbS {ρ : Fin 11 → ℕ} {ok : Bool} {d : Fin 3} {j : ℕ} (h : ok = true → 1 ≤ ρ rQ + d) :
    (nbS (k := M.k) ok d j).Ok ρ := by
  unfold nbS; split_ifs with hok
  · exact h hok
  · trivial

/-- A previous-instruction source satisfies its side condition when `I ≥ 1` whenever it is used. -/
theorem ok_chS {ρ : Fin 11 → ℕ} {ok : Bool} {j : ℕ} (h : ok = true → 1 ≤ ρ rI) :
    (chS (k := M.k) ok j).Ok ρ := by
  unfold chS; split_ifs with hok
  · exact h hok
  · trivial

/-- The previous-snapshot sources satisfy their side condition when `LB ≥ 1` after the first step.
-/
theorem ok_psnS {ρ : Fin 11 → ℕ} {W : ℕ} {t0 : Bool} (h : t0 = false → 1 ≤ ρ rLB) :
    ∀ s ∈ psnS (k := M.k) W t0, s.Ok ρ := by
  intro s hs
  simp only [psnS, List.mem_map, List.mem_range] at hs
  obtain ⟨j, -, rfl⟩ := hs
  cases t0
  · exact h rfl
  · trivial

/-- The symbolic sources of a work cell satisfy their side conditions. -/
theorem ok_cellS {ρ : Fin 11 → ℕ} {W : ℕ} {t0 rlo rT rhi : Bool}
    (hq : t0 = false → rlo = true → 1 ≤ ρ rQ) (hi : rlo = true → 1 ≤ ρ rI)
    (hlb : t0 = false → 1 ≤ ρ rLB) :
    ∀ s ∈ cellS (k := M.k) W t0 rlo rT rhi, s.Ok ρ := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | trivial
      | exact ok_nbS M (fun h => by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
          first | (simp; exact hq h.1 h.2) | simp)
      | exact ok_chS M hi
  · exact ok_psnS M hlb s hs

/-- The symbolic sources of an input position satisfy their side conditions. -/
theorem ok_inpS {ρ : Fin 11 → ℕ} {W : ℕ} {t0 p0 p1 pN1 : Bool} {lay : Fin 3}
    (hq : t0 = false → p0 = false → 1 ≤ ρ rQ) (hi : p0 = false → 1 ≤ ρ rI)
    (hlb : t0 = false → 1 ≤ ρ rLB) (hlay : (layS (k := M.k) lay).Ok ρ) :
    ∀ s ∈ inpS (k := M.k) W t0 p0 p1 pN1 lay, s.Ok ρ := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | trivial
      | exact hlay
      | exact ok_nbS M (fun h => by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
          first | (simp; exact hq h.1 h.2) | simp)
      | exact ok_chS M (fun h => hi (by simpa using h))
  · exact ok_psnS M hlb s hs

/-- The symbolic sources of a snapshot satisfy their side conditions. -/
theorem ok_snapS {ρ : Fin 11 → ℕ} {W : ℕ} {t0 : Bool} (hi : 1 ≤ ρ rI)
    (hlb : t0 = false → 1 ≤ ρ rLB) : ∀ s ∈ snapS (k := M.k) W t0, s.Ok ρ := by
  intro s hs
  simp only [snapS, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange, true_and] at hs
  rcases hs with ((rfl | rfl | rfl | rfl) | ⟨τ, rfl | rfl⟩) | hs
  · trivial
  · cases t0
    · exact hlb rfl
    · trivial
  · exact hi
  · exact hi
  · trivial
  · trivial
  · exact ok_psnS M hlb s hs

/-! ## The three kinds of tableau instructions -/

/-- The gate bits of instruction `i` of the uniform tableau circuit `cfgTab M n z T`. -/
noncomputable def ibits (n : ℕ) (z : List Bool) (T i : ℕ) : List Bool :=
  gbits (tabInstrGates (cfgArity M) (cfgWidth M) (cfgF M) n z i
    (cfgInstr M (tabLayout (z.length + n)) T i))

/-- An instruction template of a tableau instruction prints its gate bits, given its
symbolic sources. -/
theorem prog_instr_bits {n : ℕ} {z : List Bool} {T : ℕ} (θ : Tpl M.k)
    (hθ : tmpl M θ = instrOps M θ) (e : ER) (hn : e.nc = n) (hz : e.z = z.length)
    (hlt : e.i < (T + 1) * cfgStride M (z.length + n) T) (srcs : List BitSrc)
    (hins : cfgInstr M (tabLayout (z.length + n)) T e.i = ⟨θ.kind, padSrcs M srcs⟩)
    (hs : (θ.srcs (snapWidth M) (cfgArity M)).map (SSrc.toBitSrc e.f) = padSrcs M srcs)
    (hok : ∀ s ∈ θ.srcs (snapWidth M) (cfgArity M), s.Ok e.f) :
    (tmpl M θ).flatMap (MOp.exec e.f) = ibits M n z T e.i := by
  have hwf := cfgProg_wf (T := T) (tabLayout_valid (z.length + n) (cfgWidth M))
  have hlt' : e.i < (cfgProg M (tabLayout (z.length + n)) T).length := by
    rw [length_cfgProg, length_tabLayout]; exact hlt
  have hget := cfgProg_getElem M (tabLayout (z.length + n)) T hlt'
  rw [ibits, instr_bits M θ hθ e hn hz (cfgInstr M (tabLayout (z.length + n)) T e.i)
    (by rw [hins]) (by rw [hins]; exact hs)]
  · have := hwf.2 _ (List.getElem_mem hlt')
    rwa [hget] at this
  · exact hok
  · intro s hs'
    exact hwf.1 e.i hlt' s (by rw [hget]; exact hs')

/-- `Q` points at the same cell one step earlier. -/
private theorem prev_eq {S t a q : ℕ} (ht : t ≠ 0) (h : q + S = t * S + a) : q = (t -
    1) * S + a := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Nat.succ_mul] at h; simp only [Nat.add_sub_cancel]; omega

/-- **A work-cell template prints the cell's gates**, when the registers point at the cell
and the flags of the phase match the cell's position.

**Proof sketch.** The cell's instruction in `cfgProg` is `cellSrcs` padded
(`cfgPos_cellIdx`); its symbolic sources denote these (`cellS_toBitSrc`) and satisfy their
side conditions (`ok_cellS`), so `prog_instr_bits` applies. -/
theorem cell_bits {n : ℕ} {z : List Bool} {T t r : ℕ} {τ : Fin M.k} (ph : Fin 5)
    (hr : r < 2 * T + 1) (ht : t ≤ T) (e : ER) (hn : e.nc = n) (hz : e.z = z.length)
    (hI : e.i = cellIdx M (z.length + n) T t τ r)
    (hQ : t ≠ 0 → e.q + cfgStride M (z.length + n) T = e.i)
    (hLB : e.lb = t * cfgStride M (z.length + n) T)
    (h0 : decide (ph ≠ 0) = decide (1 ≤ r)) (h2 : decide (ph = 2) = decide (r = T))
    (h4 : decide (ph ≠ 4) = decide (r + 1 < 2 * T + 1)) :
    (tmpl M (.cell τ (decide (t = 0)) ph)).flatMap (MOp.exec e.f) = ibits M n z T e.i := by
  have hQ' : t ≠ 0 → e.f rQ = cellIdx M (z.length + n) T (t - 1) τ r := by
    intro h0'; have := hQ h0'; simp only [ER.f_q]; rw [hI] at this; simp only [cellIdx] at this ⊢
    have := prev_eq (S := cfgStride M (z.length + n) T) (t := t) (q := e.q)
      (a := τ * (2 * T + 1) + r) h0' (by omega)
    omega
  refine prog_instr_bits M _ rfl e hn hz ?_ (cellSrcs M (tabLayout (z.length + n)) T t τ r) ?_ ?_ ?_
  · rw [hI]
    exact (cellIdx_lt_succ M (z.length + n) T t τ hr).trans_le (Nat.mul_le_mul_right _ (by omega))
  · simp [cfgInstr, hI, length_tabLayout, cfgPos_cellIdx M (z.length + n) T t τ hr, Tpl.kind]
  · simp only [Tpl.srcs, h0, h2, h4, padS_toBitSrc]
    rw [cellS_toBitSrc M (tabLayout (z.length + n)) (length_tabLayout (z.length + n)) (by simpa
        using hI) hQ'
      (by simpa using hLB), padSrcs]
  · apply ok_padS M
    simp only [h0, h2, h4]
    apply ok_cellS M
    · intro ht0 hr1
      rw [hQ' (by simpa using ht0), cellIdx]
      simp at hr1; omega
    · intro hr1; simp only [ER.f_i, hI, cellIdx]; simp at hr1; omega
    · intro ht0; simp only [ER.f_lb, hLB]
      have : t ≠ 0 := by simpa using ht0
      have : 1 ≤ cfgStride M (z.length + n) T := by unfold cfgStride; omega
      exact Nat.mul_pos (Nat.pos_of_ne_zero ‹_›) this

/-- **An input-position template prints the position's gates**, when the registers point at
the position, the phase's flags match it and its layout source is the given one.

**Proof sketch.** As for `cell_bits`: `cfgPos_inpIdx`, `inpS_toBitSrc`, `ok_inpS`, then
`prog_instr_bits`. -/
theorem inp_bits {n : ℕ} {z : List Bool} {T t p : ℕ} (ph : IPh) (hp : p < z.length + n + 2)
    (ht : t ≤ T) (e : ER) (hn : e.nc = n) (hz : e.z = z.length)
    (hI : e.i = inpIdx M (z.length + n) T t p)
    (hQ : t ≠ 0 → e.q + cfgStride M (z.length + n) T = e.i)
    (hLB : e.lb = t * cfgStride M (z.length + n) T)
    (hph : inpPhS (k := M.k) (snapWidth M) (decide (t = 0)) ph =
      inpS (snapWidth M) (decide (t = 0)) (decide (p = 0)) (decide (p = 1))
        (decide (p = z.length + n + 1)) ph.lay)
    (hlay : (layS (k := M.k) ph.lay).toBitSrc e.f = if 1 ≤ p ∧ p ≤ z.length + n then (tabLayout
        (z.length + n)).getD (p - 1) (.const false)
          else .const false)
    (hlayok : (layS (k := M.k) ph.lay).Ok e.f) :
    (tmpl M (.inp (decide (t = 0)) ph)).flatMap (MOp.exec e.f) = ibits M n z T e.i := by
  have hQ' : t ≠ 0 → e.f rQ = inpIdx M (z.length + n) T (t - 1) p := by
    intro h0'; have := hQ h0'; simp only [ER.f_q]; rw [hI] at this; simp only [inpIdx] at this ⊢
    have := prev_eq (S := cfgStride M (z.length + n) T) (t := t) (q := e.q)
      (a := M.k * (2 * T + 1) + p) h0' (by omega)
    omega
  refine prog_instr_bits M _ rfl e hn hz ?_ (inpSrcs M (tabLayout (z.length + n)) T t p) ?_ ?_ ?_
  · rw [hI]
    exact (inpIdx_lt_succ M (z.length + n) T t hp).trans_le (Nat.mul_le_mul_right _ (by omega))
  · simp [cfgInstr, hI, length_tabLayout, cfgPos_inpIdx M (z.length + n) T t hp, Tpl.kind]
  · simp only [Tpl.srcs, hph, padS_toBitSrc]
    rw [inpS_toBitSrc M (tabLayout (z.length + n)) (length_tabLayout (z.length + n)) hp (by simpa
        using hI) hQ'
      (by simpa using hLB) _ hlay, padSrcs]
  · apply ok_padS M
    simp only [hph]
    apply ok_inpS M
    · intro ht0 hp0
      rw [hQ' (by simpa using ht0), inpIdx]
      simp at hp0; omega
    · intro hp0; simp only [ER.f_i, hI, inpIdx]; simp at hp0; omega
    · intro ht0; simp only [ER.f_lb, hLB]
      have : t ≠ 0 := by simpa using ht0
      have : 1 ≤ cfgStride M (z.length + n) T := by unfold cfgStride; omega
      exact Nat.mul_pos (Nat.pos_of_ne_zero ‹_›) this
    · exact hlayok

/-- **A snapshot template prints the snapshot's gates.** -/
theorem snap_bits {n : ℕ} {z : List Bool} {T t : ℕ} (ht : t ≤ T) (e : ER) (hn : e.nc = n)
    (hz : e.z = z.length) (hT : e.t = T) (hI : e.i = snapIdx M (z.length + n) T t)
    (hLB : e.lb = t * cfgStride M (z.length + n) T) :
    (tmpl M (.snap (decide (t = 0)))).flatMap (MOp.exec e.f) = ibits M n z T e.i := by
  refine prog_instr_bits M _ rfl e hn hz ?_ (snapSrcs M (tabLayout (z.length + n)) T t) ?_ ?_ ?_
  · rw [hI]
    exact (snapIdx_lt_succ M (z.length + n) T t).trans_le (Nat.mul_le_mul_right _ (by omega))
  · simp [cfgInstr, hI, length_tabLayout, cfgPos_snapIdx M (z.length + n) T t, Tpl.kind]
  · simp only [Tpl.srcs, padS_toBitSrc]
    rw [snapS_toBitSrc M (tabLayout (z.length + n)) (length_tabLayout (z.length + n)) (by simpa
        using hI)
      (by simpa using hT) (by simpa using hLB), padSrcs]
  · apply ok_padS M
    apply ok_snapS M
    · simp only [ER.f_i, hI, snapIdx]; omega
    · intro ht0; simp only [ER.f_lb, hLB]
      have : t ≠ 0 := by simpa using ht0
      have : 1 ≤ cfgStride M (z.length + n) T := by unfold cfgStride; omega
      exact Nat.mul_pos (Nat.pos_of_ne_zero ‹_›) this

end UTab

end Complexity
