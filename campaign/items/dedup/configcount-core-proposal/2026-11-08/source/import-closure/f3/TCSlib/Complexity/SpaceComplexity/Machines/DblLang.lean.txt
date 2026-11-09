/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading the unary length in logarithmic space

The abstract register machines of `TCSlib.Complexity.SpaceComplexity.Machines.ARM` see their
input `⟨1ⁿ, w⟩` only through comparisons with `w` and through calls to logspace deciders on
`⟨1ⁿ, …⟩`; none of their instructions measures `n`. This file supplies the missing base
decider, written directly as a register-tape program: it counts the leading run `1²ⁿ` of
`⟨1ⁿ, w⟩ = 1²ⁿ 0 1 w` into a binary register and compares the register with `w`
[AB09, §4.1: a logspace machine keeps a counter of `O(log n)` bits].

The decider is generic logspace material; its first client is [AB09, Thm 6.15]
(`TCSlib.Complexity.CircuitComplexity.LogspaceTableau`).

## Main definitions

* `Complexity.LogProg.dblLang` — the inputs `⟨1ⁿ, bits (2n)⟩`.
* `Complexity.LogProg.Dbl.prog` — the register-tape program deciding it.

## Main results

* `Complexity.LogProg.dblLang_mem` — `dblLang ∈ L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The inputs `⟨1ⁿ, bits (2n)⟩`: the index on the input is twice the unary length. -/
def dblLang : Language Bool :=
  {y | ∃ n, y = pairEncode (List.replicate n true) (Nat.bits (2 * n))}

namespace Dbl

/-- The states of the counting program. -/
inductive St where
  | vU0 | vU1 | vS | vW0 | vWF | vWT | rw1 | rw2 | cnt | iC | iB | sw1 | sw2
  | jK | jK2 | jC | jRB (b : Bool) | jI1 (b : Bool) | jI2 (b : Bool) | yes | no
  deriving DecidableEq, Fintype

/-- The transitions: the format check (`vU0` … `rw2`), the count of the leading `1`s
(`cnt`, with the increment fragment `iC`, `iB`), the rewind (`sw1`, `sw2`), and the
comparison of the counter with the index (`jK` … `jI2`). -/
def tr : St → Option Bool → (Fin 1 → Option Bool) → Action 1 Bool St
  | .vU0, a, _ => valUAct 0 .vU0 .vU1 .vS false a
  | .vU1, a, _ => valUAct 0 .vU0 .vU1 .vS true a
  | .vS, a, _ => valSAct 0 .vW0 a
  | .vW0, a, _ => valWAct 0 .vWF .vWT .rw1 none a
  | .vWF, a, _ => valWAct 0 .vWF .vWT .rw1 (some false) a
  | .vWT, a, _ => valWAct 0 .vWF .vWT .rw1 (some true) a
  | .rw1, _, _ => xAct 0 (-1) 0 .rw2
  | .rw2, a, _ => rw2Act 0 .rw2 .cnt a
  | .cnt, a, _ => if a = some true then xAct 0 1 0 .iC else xAct 0 0 0 .sw1
  | .iC, _, w => incCAct 0 .iC .iB (w 0)
  | .iB, _, w => incBAct 0 .iB .cnt (w 0)
  | .sw1, _, _ => xAct 0 (-1) 0 .sw2
  | .sw2, a, _ => rw2Act 0 .sw2 .jK a
  | .jK, a, _ => skipAct 0 .jK .jK2 a
  | .jK2, _, _ => xAct 0 1 0 .jC
  | .jC, a, w => cmpAct 0 .jC St.jRB a (w 0)
  | .jRB b, _, w => backAct 0 (.jRB b) (.jI1 b) (w 0)
  | .jI1 b, _, _ => xAct 0 (-1) 0 (.jI2 b)
  | .jI2 b, a, _ => rewAct 0 (.jI2 b) (if b then .yes else .no) a
  | .yes, _, _ => retAct true
  | .no, _, _ => retAct false

/-- **The counting program** (one register, no calls). -/
def prog : RProg 1 0 St where
  tm := ⟨.vU0, tr⟩
  call := fun _ => none

/-- The (empty) oracle. -/
def o : Fin 0 → List Bool → Bool := fun j => j.elim0

variable {y : List Bool}

/-- The configuration in state `s`, input head `ip`, register holding `bits v` with its head at
`q`, nothing written. -/
def K (s : St) (ip : Fin (y.length + 2)) (v : ℕ) (q : ℤ) : Cfg 1 Bool St y :=
  ⟨some s, ip, fun _ => FinTM.bufferTape (Nat.bits v), fun _ => q, []⟩

/-- The input-scanning view of a counting configuration is a counting configuration. -/
lemma xCfg_K (s s' : St) (ip ip' : Fin (y.length + 2)) (v : ℕ) (q q' : ℤ) :
    xCfg (K s' ip' v q') s ip 0 q = K s ip v q := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r; rw [Fin.fin_one_eq_zero r]; simp [xCfg, K]

/-- The register view of a counting configuration is a counting configuration. -/
lemma regCfg_K (s s' : St) (ip : Fin (y.length + 2)) (v v' : ℕ) (q q' : ℤ) :
    regCfg (K s' ip v q') s 0 (FinTM.bufferTape (Nat.bits v')) q = K s ip v' q := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, K]
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, K]

/-- A run from `c` to `c'` with the register head in `[-1, W]`. -/
def Rch (W : ℕ) (c c' : Cfg 1 Bool St y) : Prop :=
  ∃ T, rrun prog o c T = c' ∧ ∀ t < T, -1 ≤ (rrun prog o c t).workTapePos 0 ∧
    (rrun prog o c t).workTapePos 0 ≤ W

/-- Runs compose. -/
lemma Rch.trans {W : ℕ} {a b c : Cfg 1 Bool St y} (h₁ : Rch W a b) (h₂ : Rch W b c) :
    Rch W a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- One input-scanning step. -/
lemma step_x (s s' : St) (ip : Fin (y.length + 2)) (v : ℕ) (q : ℤ) (mvI : SignType)
    (h : ∀ w, tr s (inSym y ip.val) w = xAct 0 mvI 0 s') :
    rrun prog o (K s ip v q) 1 = K s' (moveInputPos ip mvI) v q := by
  rw [← xCfg_K s s ip ip v q q, rrun_one_x prog o _ s ip 0 q rfl]
  change (tr s (inSym y ip.val) _).apply _ = _
  rw [h, apply_xAct]
  simp only [SignType.coe_zero, add_zero]
  exact xCfg_K _ _ _ _ _ _ _

/-- The symbols of `⟨1ⁿ, w⟩`: `1` before position `2n`, `0` at `2n`. -/
lemma sym_lt {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) {k : ℕ}
    (hk : k < 2 * n) : y[k]? = some true := by
  subst hy
  rw [pairEncode_eq_dbl, dbl_replicate, List.append_assoc,
    List.getElem?_append_left (by simpa using hk)]
  simp [hk]

/-- The separator `0` of `⟨1ⁿ, w⟩` sits at position `2n`. -/
lemma sym_eq {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    y[2 * n]? = some false := by
  subst hy
  rw [pairEncode_eq_dbl, dbl_replicate, List.append_assoc,
    List.getElem?_append_right (by simp)]
  simp

/-- The length of `⟨1ⁿ, w⟩` is `2n + 2 + |w|`. -/
lemma length_eq {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    y.length = 2 * n + 2 + w.length := by
  subst hy; simp [pairEncode_eq_dbl, dbl_replicate]; omega

/-- **The counting loop**: from `cnt` at input position `1` with counter `0`, the program
reaches `cnt` at position `1 + j` with counter `j`, for every `j ≤ 2n`.

**Proof sketch.** Induction on `j`: one `cnt` step reads a `1` and moves right, then the
increment fragment (`inc_run`) adds one to the counter; the register head stays within
`|bits (2n)|` since `j + 1 ≤ 2n` (`length_bits_mono`). -/
lemma count {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    ∀ j (hj : j ≤ 2 * n), Rch (Nat.bits (2 * n)).length
      (K (y := y) .cnt ⟨1, by have := length_eq hy; omega⟩ 0 0)
      (K (y := y) .cnt ⟨1 + j, by have := length_eq hy; omega⟩ j 0) := by
  have hl := length_eq hy
  intro j
  induction j with
  | zero => intro _; exact ⟨0, rfl, fun t ht => by omega⟩
  | succ j ih =>
    intro hj
    refine (ih (by omega)).trans ?_
    have h1 : rrun prog o (K .cnt ⟨1 + j, by omega⟩ j 0) 1 =
        K (y := y) .iC ⟨2 + j, by omega⟩ j 0 := by
      rw [step_x .cnt .iC _ j 0 1 (fun w => by
        simp only [tr, show 1 + j = j + 1 by omega, inSym_succ, sym_lt hy (by omega : j < 2 * n),
          ↓reduceIte])]
      congr 1; exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    obtain ⟨T, h2, hm2⟩ := inc_run prog o 0 .iC .iB .cnt (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
      (K (y := y) .iC ⟨2 + j, by omega⟩ j 0) j
    rw [regCfg_K, regCfg_K] at h2
    refine ⟨1 + T, ?_, fun t ht => ?_⟩
    · rw [rrun_add, h1, h2]; congr 1; exact Fin.ext (by simp; omega)
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        simp [rrun_zero, K]
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, h1]
        obtain ⟨s, f, q, hq, -, hq1, hq2⟩ := hm2 t' (by omega)
        rw [regCfg_K] at hq
        rw [hq]
        have := length_bits_mono (show j + 1 ≤ 2 * n by omega)
        simp only [regCfg, Function.update_self]
        omega

/-- The initial configuration. -/
lemma init_eq : (Cfg.init (k := 1) St.vU0 y) = K .vU0 ⟨1, by omega⟩ 0 0 := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext r z; simp [K, Nat.zero_bits]

/-- **The run on a well-formed input** `⟨1ⁿ, w⟩`: the program answers whether `w = bits (2n)`,
the register head staying in `[-1, |bits (2n)|]`.

**Proof sketch.** The format check (`valPlain_run`) returns to position `1`; the counting
loop (`count`) leaves `bits (2n)` in the register at the separator; the rewind
(`rewind_x`) and the comparison (`jeqPlain_run`) decide `w = bits (2n)`; one step answers. -/
lemma run_valid {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w)
    (hw : Canon w) :
    Rch (Nat.bits (2 * n)).length (K .vU0 ⟨1, by omega⟩ 0 0)
      (K (y := y) (if w = Nat.bits (2 * n) then .yes else .no) ⟨1, by omega⟩ (2 * n) 0) := by
  have hl := length_eq hy
  set W := (Nat.bits (2 * n)).length
  -- the format check
  have h1 : Rch W (K .vU0 ⟨1, by omega⟩ 0 0) (K (y := y) .cnt ⟨1, by omega⟩ 0 0) := by
    obtain ⟨T, e, hm⟩ := (valPlain_run (P := prog) (oracle := o) (r := 0) (vU0 := .vU0)
      (vU1 := .vU1) (vS := .vS) (vW0 := .vW0) (vWF := .vWF) (vWT := .vWT) (rw₁ := .rw1)
      (rw₂ := .rw2) (next := .cnt) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a _ => by cases a <;> rfl) rfl rfl rfl rfl rfl rfl rfl rfl
      (K (y := y) .vU0 ⟨1, by omega⟩ 0 0) 0).1 ⟨n, w, hy, hw⟩
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, hs, -⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp [K]
  -- the count
  have h2 := count hy (2 * n) le_rfl
  -- the separator
  have h3 : Rch W (K (y := y) .cnt ⟨1 + 2 * n, by omega⟩ (2 * n) 0)
      (K .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0) := by
    refine ⟨1, ?_, fun t ht => ?_⟩
    · rw [step_x .cnt .sw1 _ _ 0 0 (fun _ => by
        simp only [tr, show 1 + 2 * n = 2 * n + 1 by omega, inSym_succ, sym_eq hy]; rfl)]
      rw [moveInputPos_zero]
    · obtain rfl : t = 0 := by omega
      simp [rrun_zero, K]
  -- the rewind
  have h4 : Rch W (K (y := y) .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0)
      (K .jK ⟨1, by omega⟩ (2 * n) 0) := by
    obtain ⟨T, e, hm⟩ := rewind_x prog o (K (y := y) .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0) 0 0
      .sw1 .sw2 .jK (fun _ _ => rfl) (fun a _ => by cases a <;> rfl) rfl rfl
      ⟨1 + 2 * n, by omega⟩
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, hs, -⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp [K]
  -- the comparison
  have h5 : Rch W (K (y := y) .jK ⟨1, by omega⟩ (2 * n) 0)
      (K (if w = Nat.bits (2 * n) then .yes else .no) ⟨1, by omega⟩ (2 * n) 0) := by
    obtain ⟨T, e, hm⟩ := jeqPlain_run (P := prog) (oracle := o) (r := 0) (jK := .jK)
      (jK2 := .jK2) (jC := .jC) (jRB := St.jRB) (jI1 := St.jI1) (jI2 := St.jI2) (yes := .yes)
      (no := .no) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (K (y := y) .jK ⟨1, by omega⟩ (2 * n) 0) n w hy (2 * n) rfl
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, q, hs, -, hq1, hq2⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp only [K]; exact ⟨hq1, hq2⟩
  exact (((h1.trans h2).trans h3).trans h4).trans h5

/-- The answering step. -/
lemma ret_step (b : Bool) (ip : Fin (y.length + 2)) (v : ℕ) :
    (rrun prog o (K (if b then .yes else .no) ip v 0) 1).state = none ∧
      (rrun prog o (K (if b then .yes else .no) ip v 0) 1).output = [b] ∧
      (rrun prog o (K (if b then .yes else .no) ip v 0) 1).workTapePos 0 = 0 := by
  rw [rrun_one, rstep_noncall prog o _ _ rfl rfl]
  cases b <;> simp [MultiTapeTM.step, K, prog, tr, retAct, Action.apply]

/-- The trivial decider bank (no deciders are called). -/
def nilTM : MultiTapeTM 0 Bool Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩

end Dbl

open Dbl in
/-- **`dblLang` is in `L`**: the counting program decides it with one binary counter.

**Proof sketch.** On a well-formed input `⟨1ⁿ, w⟩` the run is `Dbl.run_valid` followed by the
answering step; on any other input the format check rejects (`valPlain_run`) with the
register untouched. The register head stays in `[-1, |bits |y||]`, so `compile_space` bounds
the space by `|bits |y|| + 2 ≤ 3 logSpace |y|` (there are no deciders). -/
theorem dblLang_mem : dblLang ∈ LOGSPACE := by
  refine ⟨3, compileFinTM prog .vU0 nilTM (fun _ => ()), fun y => ?_⟩
  set W := (Nat.bits y.length).length with hW
  have key : ∃ N, (rrun prog o (Cfg.init .vU0 y) N).state = none ∧
      (rrun prog o (Cfg.init .vU0 y) N).output =
        [MultiTapeTM.indicator (dblLang : Set (List Bool)) y] ∧
      ∀ t ≤ N, -1 ≤ (rrun prog o (Cfg.init .vU0 y) t).workTapePos 0 ∧
        (rrun prog o (Cfg.init .vU0 y) t).workTapePos 0 ≤ W := by
    rw [init_eq]
    by_cases hv : ValidPlain y
    · obtain ⟨n, w, hy, hw⟩ := hv
      have hl := length_eq hy
      obtain ⟨T, e, hm⟩ := run_valid hy hw
      obtain ⟨r1, r2, r3⟩ := ret_step (y := y) (decide (w = Nat.bits (2 * n))) ⟨1, by omega⟩
        (2 * n)
      have hW' : (Nat.bits (2 * n)).length ≤ W := length_bits_mono (by omega)
      have hind : MultiTapeTM.indicator (dblLang : Set (List Bool)) y =
          decide (w = Nat.bits (2 * n)) := by
        rw [indicator_eq_decide]
        refine decide_eq_decide.mpr ⟨fun ⟨n', h⟩ => ?_, fun h => ⟨n, by rw [hy, h]⟩⟩
        have := pairEncode_injective (a₁ := (List.replicate n true, w))
          (a₂ := (List.replicate n' true, Nat.bits (2 * n'))) (hy.symm.trans h)
        simp only [Prod.mk.injEq] at this
        obtain ⟨h1, h2⟩ := this
        have : n = n' := by simpa using congrArg List.length h1
        subst this; exact h2
      simp only [decide_eq_true_eq] at r1 r2 r3
      refine ⟨T + 1, ?_, ?_, fun t ht => ?_⟩
      · rw [rrun_add, e]; convert r1 using 4
      · rw [rrun_add, e, hind]; convert r2 using 4
      · rcases Nat.lt_or_ge t T with h | h
        · have := hm t h; omega
        · rcases Nat.lt_or_ge t (T + 1) with h' | h'
          · obtain rfl : t = T := by omega
            rw [e]; simp [K]
          · obtain rfl : t = T + 1 := by omega
            rw [rrun_add, e]
            have : (rrun prog o (K (y := y) (if w = Nat.bits (2 * n) then .yes else .no)
                ⟨1, by omega⟩ (2 * n) 0) 1).workTapePos 0 = 0 := by
              convert r3 using 4
            rw [this]; omega
    · obtain ⟨T, e1, e2, e3, hm⟩ := (valPlain_run (P := prog) (oracle := o) (r := 0)
        (vU0 := .vU0) (vU1 := .vU1) (vS := .vS) (vW0 := .vW0) (vWF := .vWF) (vWT := .vWT)
        (rw₁ := .rw1) (rw₂ := .rw2) (next := .cnt) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun a _ => by cases a <;> rfl) rfl rfl rfl rfl rfl rfl rfl rfl
        (K (y := y) .vU0 ⟨1, by omega⟩ 0 0) 0).2 hv
      rw [xCfg_K] at e1 e2 e3 hm
      have hn : MultiTapeTM.indicator (dblLang : Set (List Bool)) y = false := by
        rw [indicator_eq_decide]
        simp only [decide_eq_false_iff_not]
        rintro ⟨n, rfl⟩
        exact hv ⟨n, _, rfl, canon_bits _⟩
      refine ⟨T, e1, by rw [e2, hn]; rfl, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t T with h | h
      · obtain ⟨s, ip, hs, -⟩ := hm t h
        rw [xCfg_K] at hs
        rw [hs]; simp [K]
      · obtain rfl : t = T := by omega
        rw [e3]; simp [K]
  obtain ⟨N, h1, h2, hbox⟩ := key
  obtain ⟨T, hT, hsp⟩ := compile_space prog .vU0 nilTM (fun _ => ()) o (fun _ => -1)
    (fun _ => (W : ℤ)) 0 N _ h1 h2
    (fun t ht r => by rw [Fin.fin_one_eq_zero r]; exact hbox t ht)
    (fun t _ l cs _ hcs => by simp [prog] at hcs)
  refine ⟨T, hT, hsp.trans ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, zero_mul,
    add_zero]
  have e1 := length_bits_le_log y.length
  have : ((W : ℤ) - -1 + 1).toNat = W + 2 := by omega
  rw [this]
  simp only [logSpace]
  omega

end Complexity.LogProg
