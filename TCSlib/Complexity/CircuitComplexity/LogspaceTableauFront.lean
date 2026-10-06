/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.ClassNP.CounterProgPolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The front end of the uniform tableau emitter as a counter program

The emitter of the uniform tableau circuits (`Complexity.UTab.tabEmit`) reads its input
`1ⁿ 0 1ᵀ 0` with the time bound `T = (C + 1)(n + 1)^d` in unary. This file gives a counter
program (`Complexity.CounterProg`) that writes this input from `1ⁿ`: it copies `1ⁿ`, then
computes `T` by repeated multiplication with count-down loops, and prints it. Being a counter
program with polynomially many steps, it is simulated in logarithmic space
(`TCSlib.Complexity.SpaceComplexity.CounterProgSimRun`), which is how the emitter's
input is made available to the logspace simulation of the emitter [AB09, Remark 6.7].

## Main definitions

* `Complexity.UTab.Front.prog C d` — the program; `Complexity.UTab.Front.word C d n` its output.

## Main results

* `Complexity.UTab.Front.run_word` — on `1ⁿ` the program halts within
  `Complexity.UTab.Front.bnd C d · (n + 1)^{d + 1}` steps with output `1ⁿ 0 1ᵀ 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.1.1, Remark 6.7.)
-/

namespace Complexity

namespace UTab.Front

open CounterProg

/-- The labels of the front end: reading, constant loading (`ldA`, `ldD`), the
multiplication loops, printing. -/
inductive Lb (C d : ℕ) where
  | rN | rN1 | rN2 | e0 | e1
  | ldA (i : Fin (C + 2))
  | ldD (i : Fin (d + 1))
  | dh | dd | mh | md | xh | xd | x1 | x2 | th | tdl | t1 | bh | bd | b1
  | fin | fin2 | fin3
  deriving DecidableEq, Fintype

/-- Register `X` (`n + 1`). -/
abbrev rX : Fin 5 := 0
/-- Register `A` (the product). -/
abbrev rA : Fin 5 := 1
/-- Register `B` (the new product). -/
abbrev rB : Fin 5 := 2
/-- Register `Tm` (scratch copy of `X`). -/
abbrev rTm : Fin 5 := 3
/-- Register `D` (multiplications left). -/
abbrev rD : Fin 5 := 4

variable (C d : ℕ)

/-- **The front end.** Read `1ⁿ` into `X` while printing it, print `0`, set `X = n + 1`,
`A = C + 1`, `D = d`; `d` times replace `A` by `A · X` (`A` count-down: add `X` to `B` through
the scratch `Tm`; then move `B` to `A`); print `A` in unary and `0`. -/
def prog : Lb C d → Instr 5 (Lb C d)
  | .rN => .rd .e0 .e0 .rN1
  | .rN1 => .inc rX .rN2
  | .rN2 => .out true .rN
  | .e0 => .out false .e1
  | .e1 => .inc rX (.ldA ⟨0, by omega⟩)
  | .ldA i =>
    if h : i.val < C + 1 then .inc rA (.ldA ⟨i.val + 1, by omega⟩)
    else .goto (.ldD ⟨0, by omega⟩)
  | .ldD i => if h : i.val < d then .inc rD (.ldD ⟨i.val + 1, by omega⟩) else .goto .dh
  | .dh => .jz rD .fin .dd
  | .dd => .dec rD .mh
  | .mh => .jz rA .bh .md
  | .md => .dec rA .xh
  | .xh => .jz rX .th .xd
  | .xd => .dec rX .x1
  | .x1 => .inc rB .x2
  | .x2 => .inc rTm .xh
  | .th => .jz rTm .mh .tdl
  | .tdl => .dec rTm .t1
  | .t1 => .inc rX .th
  | .bh => .jz rB .dh .bd
  | .bd => .dec rB .b1
  | .b1 => .inc rA .bh
  | .fin => .pr rA .fin2
  | .fin2 => .out false .fin3
  | .fin3 => .halt

/-- The time bound `T = (C + 1)(n + 1)^d`. -/
def tb (n : ℕ) : ℕ := (C + 1) * (n + 1) ^ d

/-- The output `1ⁿ 0 1ᵀ 0`, the input of the emitter. -/
def word (n : ℕ) : List Bool :=
  List.replicate n true ++ false :: (List.replicate (tb C d n) true ++ false :: [])

/-- The register file. -/
def rv (a b c e f : ℕ) : Fin 5 → ℕ := fun i =>
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => e
  | _ => f

/-- Reading register `X`. -/
@[simp] lemma rv_X (a b c e f : ℕ) : rv a b c e f rX = a := rfl
/-- Reading register `A`. -/
@[simp] lemma rv_A (a b c e f : ℕ) : rv a b c e f rA = b := rfl
/-- Reading register `B`. -/
@[simp] lemma rv_B (a b c e f : ℕ) : rv a b c e f rB = c := rfl
/-- Reading register `Tm`. -/
@[simp] lemma rv_Tm (a b c e f : ℕ) : rv a b c e f rTm = e := rfl
/-- Reading register `D`. -/
@[simp] lemma rv_D (a b c e f : ℕ) : rv a b c e f rD = f := rfl

/-- Writing register `X`. -/
lemma upd_X (a b c e f v : ℕ) : Function.update (rv a b c e f) rX v = rv v b c e f := by
  funext i; fin_cases i <;> simp [rv, Function.update] <;> intro h <;> exact absurd h (by decide)
/-- Writing register `A`. -/
lemma upd_A (a b c e f v : ℕ) : Function.update (rv a b c e f) rA v = rv a v c e f := by
  funext i; fin_cases i <;> simp [rv, Function.update] <;> intro h <;> exact absurd h (by decide)
/-- Writing register `B`. -/
lemma upd_B (a b c e f v : ℕ) : Function.update (rv a b c e f) rB v = rv a b v e f := by
  funext i; fin_cases i <;> simp [rv, Function.update] <;> intro h <;> exact absurd h (by decide)
/-- Writing register `Tm`. -/
lemma upd_Tm (a b c e f v : ℕ) : Function.update (rv a b c e f) rTm v = rv a b c v f := by
  funext i; fin_cases i <;> simp [rv, Function.update] <;> intro h <;> exact absurd h (by decide)
/-- Writing register `D`. -/
lemma upd_D (a b c e f v : ℕ) : Function.update (rv a b c e f) rD v = rv a b c e v := by
  funext i; fin_cases i <;> simp [rv, Function.update] <;> intro h <;> exact absurd h (by decide)

section Phases

variable {C d} {x : List Bool}

/-- The empty run. -/
lemma goes_nil (l : Lb C d) (ρ : Fin 5 → ℕ) (p : ℕ) :
    Goes (prog C d) x l ρ p (some l) ρ p [] 0 := fun o => ⟨0, le_rfl, by simp [run_zero]⟩

/-- The reading loop: after `j ≤ n` rounds, `X = j` and `1ʲ` printed. -/
lemma goes_read (n : ℕ) (hx : x = List.replicate n true) :
    ∀ j ≤ n, Goes (prog C d) x .rN (rv 0 0 0 0 0) 0 (some .rN) (rv j 0 0 0 0) j
      (List.replicate j true) (3 * j) := by
  intro j
  induction j with
  | zero => intro _; exact goes_nil _ _ _
  | succ j ih =>
    intro hj
    have h1 := goes_rd_true (P := prog C d) (x := x) (l := .rN) (ρ := rv j 0 0 0 0) (p := j)
      (le := .e0) (lf := .e0) (lt := .rN1) rfl
      (by rw [hx, List.getElem?_replicate, if_pos (by omega)])
    have h2 := goes_inc (P := prog C d) (x := x) (l := .rN1) (l' := .rN2) (r := rX)
      (ρ := rv j 0 0 0 0) (p := j + 1) rfl
    have h3 := goes_out (P := prog C d) (x := x) (l := .rN2) (l' := .rN) (b := true)
      (ρ := Function.update (rv j 0 0 0 0) rX (rv j 0 0 0 0 rX + 1)) (p := j + 1) rfl
    refine ((ih (by omega)).trans ((h1.trans h2).trans h3)).congr rfl ?_ rfl rfl ?_ (by omega)
    · rw [rv_X, upd_X]
    · simp [List.replicate_succ']

/-- A chain of increments: `lab i ↦ inc r (lab (i + 1))` for `i < K`. -/
lemma goes_incChain {lab : ℕ → Lb C d} {r : Fin 5} (K : ℕ)
    (h : ∀ i < K, prog C d (lab i) = .inc r (lab (i + 1))) (ρ : Fin 5 → ℕ) (p : ℕ) :
    ∀ i ≤ K, Goes (prog C d) x (lab 0) ρ p (some (lab i)) (Function.update ρ r (ρ r + i)) p []
      i := by
  intro i
  induction i with
  | zero => intro _; simpa using goes_nil (C := C) (d := d) (x := x) (lab 0) ρ p
  | succ i ih =>
    intro hi
    refine ((ih (by omega)).trans (goes_inc (h (i) (by omega)))).congr rfl ?_ rfl rfl (by simp)
      (by omega)
    funext j; by_cases hj : j = r
    · subst hj; simp; omega
    · simp [hj]

/-- Register files with equal entries are equal. -/
lemma rv_congr {a b c e f a' b' c' e' f' : ℕ} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : e = e') (h5 : f = f') : rv a b c e f = rv a' b' c' e' f' := by
  subst h1 h2 h3 h4 h5; rfl

/-- The copy loop: `X` is added to `B` and to `Tm`, and cleared. -/
lemma goes_xloop (x0 a b t e p : ℕ) :
    Goes (prog C d) x .xh (rv x0 a b t e) p (some .th) (rv 0 a (b + x0) (t + x0) e) p []
      (x0 * 4 + 1) := by
  have := goes_loop (P := prog C d) (x := x) (head := .xh) (dl := .xd) (body := .x1)
    (exit := .th) (r := rX) rfl rfl x0 (fun j => rv (x0 - j) a (b + j) (t + j) e) (fun _ => p)
    (fun _ => []) 2 (fun j _ => rfl) (fun j hj => by
      rw [upd_X]
      have h1 := goes_inc (P := prog C d) (x := x) (l := .x1) (l' := .x2) (r := rB)
        (ρ := rv (x0 - j - 1) a (b + j) (t + j) e) (p := p) rfl
      rw [rv_B, upd_B] at h1
      have h2 := goes_inc (P := prog C d) (x := x) (l := .x2) (l' := .xh) (r := rTm)
        (ρ := rv (x0 - j - 1) a (b + j + 1) (t + j) e) (p := p) rfl
      rw [rv_Tm, upd_Tm] at h2
      exact (h1.trans h2).congr rfl
        (rv_congr (by omega) rfl (by omega) (by omega) rfl) rfl rfl rfl le_rfl)
  refine this.congr (rv_congr (by omega) rfl (by omega) (by omega) rfl)
    (rv_congr (by omega) rfl rfl rfl rfl) rfl rfl (by simp) (by omega)

/-- The restore loop: `Tm` is added back to `X`, and cleared. -/
lemma goes_tloop (x0 a b t e p : ℕ) :
    Goes (prog C d) x .th (rv x0 a b t e) p (some .mh) (rv (x0 + t) a b 0 e) p []
      (t * 3 + 1) := by
  have := goes_loop (P := prog C d) (x := x) (head := .th) (dl := .tdl) (body := .t1)
    (exit := .mh) (r := rTm) rfl rfl t (fun j => rv (x0 + j) a b (t - j) e) (fun _ => p)
    (fun _ => []) 1 (fun j _ => rfl) (fun j hj => by
      rw [upd_Tm]
      have h1 := goes_inc (P := prog C d) (x := x) (l := .t1) (l' := .th) (r := rX)
        (ρ := rv (x0 + j) a b (t - j - 1) e) (p := p) rfl
      rw [rv_X, upd_X] at h1
      exact h1.congr rfl (rv_congr (by omega) rfl rfl (by omega) rfl) rfl rfl rfl le_rfl)
  refine this.congr (rv_congr (by omega) rfl rfl (by omega) rfl)
    (rv_congr rfl rfl rfl (by omega) rfl) rfl rfl (by simp) (by omega)

/-- The multiplication loop: `B` gains `A · X`, `A` is cleared. -/
lemma goes_aloop (x0 a b e p : ℕ) :
    Goes (prog C d) x .mh (rv x0 a b 0 e) p (some .bh) (rv x0 0 (b + a * x0) 0 e) p []
      (a * (7 * x0 + 4) + 1) := by
  have := goes_loop (P := prog C d) (x := x) (head := .mh) (dl := .md) (body := .xh)
    (exit := .bh) (r := rA) rfl rfl a (fun j => rv x0 (a - j) (b + j * x0) 0 e) (fun _ => p)
    (fun _ => []) (7 * x0 + 2) (fun j _ => rfl) (fun j hj => by
      rw [upd_A]
      exact ((goes_xloop x0 (a - j - 1) (b + j * x0) 0 e p).trans
        (goes_tloop 0 (a - j - 1) (b + j * x0 + x0) (0 + x0) e p)).congr rfl
        (rv_congr (by omega) (by omega) (by ring) (by omega) rfl) rfl rfl rfl (by omega))
  refine this.congr (rv_congr rfl (by omega) (by simp) rfl rfl)
    (rv_congr rfl (by omega) rfl rfl rfl) rfl rfl (by simp) (by ring_nf; omega)

/-- The move loop: `B` is added to `A`, and cleared. -/
lemma goes_bloop (x0 a b e p : ℕ) :
    Goes (prog C d) x .bh (rv x0 a b 0 e) p (some .dh) (rv x0 (a + b) 0 0 e) p []
      (b * 3 + 1) := by
  have := goes_loop (P := prog C d) (x := x) (head := .bh) (dl := .bd) (body := .b1)
    (exit := .dh) (r := rB) rfl rfl b (fun j => rv x0 (a + j) (b - j) 0 e) (fun _ => p)
    (fun _ => []) 1 (fun j _ => rfl) (fun j hj => by
      rw [upd_B]
      have h1 := goes_inc (P := prog C d) (x := x) (l := .b1) (l' := .bh) (r := rA)
        (ρ := rv x0 (a + j) (b - j - 1) 0 e) (p := p) rfl
      rw [rv_A, upd_A] at h1
      exact h1.congr rfl (rv_congr rfl (by omega) (by omega) rfl rfl) rfl rfl rfl le_rfl)
  refine this.congr (rv_congr rfl (by omega) (by omega) rfl rfl)
    (rv_congr rfl rfl (by omega) rfl rfl) rfl rfl (by simp) (by omega)

/-- The power loop: `d` multiplications by `X ≥ 1` turn `A = C + 1` into
`(C + 1) X^d`.

**Proof sketch.** `goes_loop` over `D`; round `j` is the multiplication loop (`goes_aloop`)
followed by the move loop (`goes_bloop`), taking `A = (C + 1) X^j` to `(C + 1) X^{j+1}`; the
cost of a round is bounded using `A · X ≤ T = (C + 1) X^d`. -/
lemma goes_dloop (x0 p : ℕ) (hx : 1 ≤ x0) :
    Goes (prog C d) x .dh (rv x0 (C + 1) 0 0 d) p (some .fin) (rv x0 ((C + 1) * x0 ^ d) 0 0 0) p []
      (d * (14 * ((C + 1) * x0 ^ d) + 4) + 1) := by
  set T := (C + 1) * x0 ^ d with hT
  have := goes_loop (P := prog C d) (x := x) (head := .dh) (dl := .dd) (body := .mh)
    (exit := .fin) (r := rD) rfl rfl d (fun j => rv x0 ((C + 1) * x0 ^ j) 0 0 (d - j))
    (fun _ => p) (fun _ => []) (14 * T + 2) (fun j _ => rfl) (fun j hj => by
      rw [upd_D]
      have hA : (C + 1) * x0 ^ j * x0 ≤ T := by
        rw [hT, mul_assoc, ← pow_succ]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by omega))
      have hA' : (C + 1) * x0 ^ j ≤ (C + 1) * x0 ^ j * x0 := Nat.le_mul_of_pos_right _ hx
      refine ((goes_aloop x0 ((C + 1) * x0 ^ j) 0 (d - j - 1) p).trans
        (goes_bloop x0 0 (0 + (C + 1) * x0 ^ j * x0) (d - j - 1) p)).congr rfl
        (rv_congr rfl (by rw [pow_succ]; ring) rfl rfl (by omega)) rfl rfl rfl ?_
      have : (C + 1) * x0 ^ j * (7 * x0 + 4) = 7 * ((C + 1) * x0 ^ j * x0) +
          4 * ((C + 1) * x0 ^ j) := by ring
      rw [this]
      simp only [Nat.zero_add]
      omega)
  refine this.congr (rv_congr rfl (by simp) rfl rfl (by omega))
    (rv_congr rfl rfl rfl rfl (by omega)) rfl rfl (by simp) (by ring_nf; omega)

end Phases

/-- The step bound constant of the front end. -/
def bnd : ℕ := 30 + C + 5 * d + 14 * d * (C + 1)

section Whole

variable {C d}

/-- The loading chain of `A`. -/
def labA (i : ℕ) : Lb C d := if h : i ≤ C + 1 then .ldA ⟨i, by omega⟩ else .ldA ⟨0, by omega⟩

/-- The loading chain of `D`. -/
def labD (i : ℕ) : Lb C d := if h : i ≤ d then .ldD ⟨i, by omega⟩ else .ldD ⟨0, by omega⟩

/-- **The front end on `1ⁿ`** halts within `bnd C d · (n + 1)^{d + 1}` steps printing
`1ⁿ 0 1ᵀ 0`, `T = (C + 1)(n + 1)^d`.

**Proof sketch.** The reading loop (`goes_read`) and the end of the input; the loading chains;
the power loop (`goes_dloop`) with `X = n + 1`; printing. The step count is
`3n + C + d + 12 + d (14T + 4)`. -/
theorem goes_front (n : ℕ) : ∃ ρ p, Goes (prog C d) (List.replicate n true) .rN (rv 0 0 0 0 0) 0
    none ρ p (word C d n) (bnd C d * (n + 1) ^ (d + 1)) := by
  set x := List.replicate n true
  have hr := goes_read (C := C) (d := d) n rfl n le_rfl
  have hend := goes_rd_end (P := prog C d) (x := x) (l := .rN) (ρ := rv n 0 0 0 0) (p := n)
    (le := .e0) (lf := .e0) (lt := .rN1) rfl (by simp [x])
  have he0 := goes_out (P := prog C d) (x := x) (l := .e0) (l' := .e1) (b := false)
    (ρ := rv n 0 0 0 0) (p := n) rfl
  have he1 := goes_inc (P := prog C d) (x := x) (l := .e1) (l' := labA (C := C) (d := d) 0)
    (r := rX)
    (ρ := rv n 0 0 0 0) (p := n) (by simp [prog, labA])
  rw [rv_X, upd_X] at he1
  have hA := goes_incChain (x := x) (lab := labA (C := C) (d := d)) (r := rA) (C + 1)
    (fun i hi => by
      simp only [labA, dif_pos (show i ≤ C + 1 by omega), dif_pos (show i + 1 ≤ C + 1 by omega),
        prog, dif_pos hi])
    (rv (n + 1) 0 0 0 0) n (C + 1) le_rfl
  rw [rv_A, upd_A] at hA
  have hA2 := goes_goto (P := prog C d) (x := x) (l := labA (C := C) (d := d) (C + 1))
    (l' := labD 0)
    (ρ := rv (n + 1) (0 + (C + 1)) 0 0 0) (p := n) (by simp [labA, labD, prog])
  have hD := goes_incChain (x := x) (lab := labD (C := C) (d := d)) (r := rD) d (fun i hi => by
      simp only [labD, dif_pos (show i ≤ d by omega), dif_pos (show i + 1 ≤ d by omega),
        prog, dif_pos hi])
    (rv (n + 1) (0 + (C + 1)) 0 0 0) n d le_rfl
  rw [rv_D, upd_D] at hD
  have hD2 := goes_goto (P := prog C d) (x := x) (l := labD (C := C) (d := d) d) (l' := .dh)
    (ρ := rv (n + 1) (0 + (C + 1)) 0 0 (0 + d)) (p := n) (by simp [labD, prog])
  have hL := goes_dloop (C := C) (d := d) (x := x) (n + 1) n (by omega)
  have hP := goes_pr (P := prog C d) (x := x) (l := .fin) (l' := .fin2) (r := rA)
    (ρ := rv (n + 1) ((C + 1) * (n + 1) ^ d) 0 0 0) (p := n) rfl
  have hO := goes_out (P := prog C d) (x := x) (l := .fin2) (l' := .fin3) (b := false)
    (ρ := rv (n + 1) ((C + 1) * (n + 1) ^ d) 0 0 0) (p := n) rfl
  have hH := goes_halt (P := prog C d) (x := x) (l := .fin3)
    (ρ := rv (n + 1) ((C + 1) * (n + 1) ^ d) 0 0 0) (p := n) rfl
  refine ⟨_, _, (((((((((((hr.trans hend).trans he0).trans he1).trans hA).trans hA2).trans
    hD).trans (Goes.congr (σ' := rv (n + 1) (C + 1) 0 0 d) hD2 rfl (by simp) rfl rfl rfl
      le_rfl)).trans hL).trans hP).trans hO).trans hH).congr rfl rfl rfl rfl ?_ ?_⟩
  · simp [word, tb]
  · -- the step count
    set Y := (n + 1) ^ d with hY
    set Z := (n + 1) ^ (d + 1) with hZ
    have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
    have hZY : Z = Y * (n + 1) := by rw [hZ, hY, pow_succ]
    have hnZ : n + 1 ≤ Z := by rw [hZY]; exact Nat.le_mul_of_pos_left _ hY1
    have hYZ : Y ≤ Z := by rw [hZY]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hZ1 : 1 ≤ Z := by omega
    have h1 : C ≤ C * Z := Nat.le_mul_of_pos_right _ hZ1
    have h2 : d ≤ d * Z := Nat.le_mul_of_pos_right _ hZ1
    have h3 : d * (C + 1) * Y ≤ d * (C + 1) * Z := Nat.mul_le_mul_left _ hYZ
    have e1 : d * (14 * ((C + 1) * Y) + 4) = 14 * (d * (C + 1) * Y) + 4 * d := by ring
    have e2 : bnd C d * Z = 30 * Z + C * Z + 5 * (d * Z) + 14 * (d * (C + 1) * Z) := by
      unfold bnd; ring
    rw [e1, e2]
    omega

/-- **The front end as a run**: on `1ⁿ` the program halts within `bnd C d · (n + 1)^{d + 1}`
steps with output `1ⁿ 0 1ᵀ 0`. -/
theorem run_word (n : ℕ) : ∃ t ≤ bnd C d * (n + 1) ^ (d + 1),
    (run (prog C d) (List.replicate n true) (init .rN) t).lbl = none ∧
    (run (prog C d) (List.replicate n true) (init .rN) t).out = word C d n := by
  obtain ⟨ρ, p, h⟩ := goes_front (C := C) (d := d) n
  obtain ⟨t, ht, hrun⟩ := h []
  have hinit : (init .rN : St 5 (Lb C d)) = ⟨some .rN, rv 0 0 0 0 0, 0, []⟩ := by
    simp only [init, St.mk.injEq, true_and, and_true]
    funext i; fin_cases i <;> rfl
  rw [hinit]
  exact ⟨t, ht, by rw [hrun], by rw [hrun]; simp⟩

end Whole

end UTab.Front

end Complexity
