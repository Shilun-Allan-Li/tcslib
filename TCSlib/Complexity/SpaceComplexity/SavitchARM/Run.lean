/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Machine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Routines of the Savitch register machine

Run lemmas for the arithmetic routines of `Complexity.LogProg.SavitchARM.A`: the loop sites
(instances of the generic loops of
`TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops`), multiplication
(`mul_run`), and the two stack operations — pushing a code as a `w`-bit digit of `SE`
together with a phase bit of `SP` (`pushV_run`, `pushU_run`), and popping the last digit of
`SE` into `E` (`pop_run`).

Infrastructure for [AB09, §4.2.1, proof of Theorem 4.14]; not itself a result of the book.

## Main results

* `Complexity.LogProg.SavitchARM.preS_A` — the machine meets the syntactic preconditions.
* `Complexity.LogProg.SavitchARM.mul_run` — `P := P · F`.
* `Complexity.LogProg.SavitchARM.pushV_run`, `pushU_run`, `pop_run` — the stack.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

variable (E : ℕ) (orc : Fin 4 → List Bool → Bool) (x : List Bool) (B : ℕ)

/-- **The Savitch machine meets the syntactic preconditions** everywhere: its equality
tests compare distinct registers and its calls have distinct arguments. -/
lemma preS_A (a : AConf 18 (Lb E)) : PreS (A E) x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l with
    | ld j => by_cases h : j.val < E <;> simp [PreS, A, h]
    | mv k j => fin_cases j <;> simp [PreS, A, mvI]
    | dm b j => fin_cases j <;> simp [PreS, A, dmI]
    | sb b j => fin_cases j <;> simp [PreS, A, sbI]
    | hv b j => fin_cases j <;> simp [PreS, A, hvI]
    | cp k j => fin_cases j <;> simp [PreS, A, cpI]
    | sh k j => fin_cases j <;> simp [PreS, A, shI]
    | _ => simp [PreS, A] <;> decide

variable {E orc x B}

/-- A bounded register file at a label meets the guard. -/
lemma gb_of {st : St} (hbd : st.Bd B) (l : Lb E) :
    GuardLe (A E) x B (some l, st.toV, none) := ⟨preS_A E x _, hbd.toV⟩

/-- One step from a bounded register file. -/
lemma step_of {st : St} {l : Lb E} {c : AConf 18 (Lb E)} (hbd : st.Bd B)
    (h : AReach (A E) orc x (GuardLe (A E) x B) (astep (A E) orc x (some l, st.toV, none)) c) :
    AReach (A E) orc x (GuardLe (A E) x B) (some l, st.toV, none) c :=
  AReach.step (gb_of hbd l) h

/-- Continue a run from an equal register file. -/
lemma cont {st st' : St} {l : Lb E} {c : AConf 18 (Lb E)} (e : st = st')
    (h : AReach (A E) orc x (GuardLe (A E) x B) (some l, st'.toV, none) c) :
    AReach (A E) orc x (GuardLe (A E) x B) (some l, st.toV, none) c := e ▸ h

/-- Continue a halting run from an equal register file. -/
lemma contH {st st' : St} {l : Lb E} {r : Bool} (e : st = st')
    (h : AHalt (A E) orc x (GuardLe (A E) x B) (some l, st'.toV, none) r) :
    AHalt (A E) orc x (GuardLe (A E) x B) (some l, st.toV, none) r := e ▸ h

/-! ## Loop sites -/

/-- Move sites have distinct registers. -/
lemma mv_ne (k : MvS) : mvSrc k ≠ mvDst k := by
  cases k <;> (try cases ‹Bool›) <;> decide

/-- **A move site** adds the source to the target and clears the source. -/
theorem mv_run (k : MvS) (st : St) (hbd : st.Bd B)
    (hb : st.toV (mvDst k) + st.toV (mvSrc k) ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.mv k 0), st.toV, none)
      (some (mvExit k), Function.update (Function.update st.toV (mvSrc k) 0) (mvDst k)
        (st.toV (mvDst k) + st.toV (mvSrc k)), none) :=
  move_run (A := A E) (oracle := orc) (x := x) (B := B) (l := .mv k 0) (l1 := .mv k 1)
    (l2 := .mv k 2) (lx := mvExit k) (mv_ne k) rfl rfl rfl _ _ rfl hbd.toV hb

/-- Copy sites have distinct registers, all different from `Z`. -/
lemma cp_ne (k : CpS) : cpSrc k ≠ cpDst k ∧ cpSrc k ≠ rZ ∧ cpDst k ≠ rZ := by
  cases k <;> (try cases ‹Bool›) <;> decide

/-- **A copy site** adds the source to the target. -/
theorem cp_run (k : CpS) (st : St) (hbd : st.Bd B) (hZ : st.Z = 0)
    (hb : st.toV (cpDst k) + st.toV (cpSrc k) ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.cp k 0), st.toV, none)
      (some (cpExit k), Function.update st.toV (cpDst k)
        (st.toV (cpDst k) + st.toV (cpSrc k)), none) :=
  copy_run (A := A E) (oracle := orc) (x := x) (B := B) (l := .cp k 0) (l1 := .cp k 1)
    (l2 := .cp k 2) (l3 := .cp k 3) (l4 := .cp k 4) (l5 := .cp k 5) (l6 := .cp k 6)
    (lx := cpExit k) (cp_ne k).1 (cp_ne k).2.1 (cp_ne k).2.2 rfl rfl rfl rfl rfl rfl rfl _ hZ
    hbd.toV hb

/-- Shift sites have distinct registers. -/
lemma sh_ne (k : ShS) : rC ≠ shReg k ∧ rC ≠ rZ ∧ shReg k ≠ rZ := by
  cases k <;> (try cases ‹Bool›) <;> decide

/-- **A shift site** multiplies its register by `2 ^ C` and clears `C`. -/
theorem sh_run (k : ShS) (st : St) (hbd : st.Bd B) (hZ : st.Z = 0)
    (hb : st.toV (shReg k) * 2 ^ st.C ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.sh k 0), st.toV, none)
      (some (shExit k), Function.update (Function.update st.toV rC 0) (shReg k)
        (st.toV (shReg k) * 2 ^ st.C), none) :=
  shl_run (A := A E) (oracle := orc) (x := x) (B := B) (l := .sh k 0) (l1 := .sh k 1)
    (l2 := .sh k 2) (l3 := .sh k 3) (l4 := .sh k 4) (l5 := .sh k 5) (l6 := .sh k 6)
    (l7 := .sh k 7) (l8 := .sh k 8) (lx := shExit k)
    (sh_ne k).1 (sh_ne k).2.1 (sh_ne k).2.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl _ _ rfl
    hZ hbd.toV hb

/-- **The doubled move site** `SP → T`. -/
theorem dm_run (b : Bool) (st : St) (hbd : st.Bd B) (hb : st.T + 2 * st.SP ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.dm b 0), st.toV, none)
      (some (.mv (.pushSP b) 0), St.toV { st with SP := 0, T := st.T + 2 * st.SP }, none) := by
  have h := dmove_run (A := A E) (oracle := orc) (x := x) (B := B) (r := rSP) (t := rT)
    (l := .dm b 0) (l1 := .dm b 1) (l2 := .dm b 2) (l3 := .dm b 3) (lx := .mv (.pushSP b) 0)
    (by decide) rfl rfl rfl rfl _ st.toV rfl hbd.toV hb
  regs at h
  exact h

/-- **The subtraction site** `SE := SE - Q`. -/
theorem sb_run (b : Bool) (st : St) (hbd : st.Bd B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.sb b 0), st.toV, none)
      (some (.mv (.popE b) 0), St.toV { st with Q := 0, SE := st.SE - st.Q }, none) := by
  have h := sub_run (A := A E) (oracle := orc) (x := x) (B := B) (q := rQ) (r := rSE)
    (l := .sb b 0) (l1 := .sb b 1) (l2 := .sb b 2) (lx := .mv (.popE b) 0)
    (by decide) rfl rfl rfl _ st.toV rfl hbd.toV
  regs at h
  exact h

/-- **The halving site** `T := T / 2 ^ C`. -/
theorem hv_run (b : Bool) (st : St) (hbd : st.Bd B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.hv b 0), st.toV, none)
      (some (.cp (.popT b) 0), St.toV { st with C := 0, T := st.T / 2 ^ st.C }, none) := by
  have h := halve_run (A := A E) (oracle := orc) (x := x) (B := B) (c := rC) (r := rT)
    (l := .hv b 0) (l1 := .hv b 1) (l2 := .hv b 2) (lx := .cp (.popT b) 0)
    (by decide) rfl rfl rfl _ st.toV rfl hbd.toV
  regs at h
  exact h

/-! ## Multiplication -/

/-- **The multiplication loop**: from `mulL f` with `C = c`, the machine adds `c · P` to `T`,
clears `C` and reaches `mulFin f`.

**Proof sketch.** Induction on `c`: each round decrements `C` and copies `P` into `T`
(`cp_run`). -/
theorem mulL_run (f : Bool) : ∀ (c : ℕ) (st : St), st.C = c → st.Z = 0 → st.Bd B →
    st.T + c * st.P ≤ B →
    AReach (A E) orc x (GuardLe (A E) x B) (some (.mulL f), st.toV, none)
      (some (.mulFin f), St.toV { st with C := 0, T := st.T + c * st.P }, none) := by
  intro c
  induction c with
  | zero =>
    intro st hC hZ hbd hb
    refine step_of hbd ?_
    regs [astep, A, hC, ↓reduceIte]
    refine reach_of_eq (AReach.refl _) ?_
    congr 3; ext <;> simp [hC]
  | succ c ih =>
    intro st hC hZ hbd hb
    have hP : st.P ≤ (c + 1) * st.P := Nat.le_mul_of_pos_left _ (by omega)
    refine step_of hbd ?_
    regs [astep, A, hC, Nat.add_one_ne_zero, ↓reduceIte]
    refine step_of hbd ?_
    regs [astep, A, hC, Nat.add_sub_cancel]
    have hbd1 : St.Bd B { st with C := c } := by simp only [St.Bd] at hbd ⊢; omega
    refine (cp_run (.mulP f) _ hbd1 hZ (by regs [cpDst, cpSrc]; omega)).trans ?_
    regs [cpDst, cpSrc, cpExit]
    have e : (c + 1) * st.P = st.P + c * st.P := by ring
    refine reach_of_eq (ih _ rfl hZ (by simp only [St.Bd] at hbd ⊢; omega)
      (by dsimp only; omega)) ?_
    congr 3; ext <;> simp; omega

/-- **Multiplication**: from `cp (mulF f)` with `C = T = Z = 0`, the machine multiplies `P`
by `F` (`F = P` if `f`, else `F = a`) and reaches the exit of the site `mulT f`.

**Proof sketch.** Copy `F` into `C` (`cp_run`), add `F · P` into `T` (`mulL_run`), clear `P`
and move `T` into it (`mv_run`). -/
theorem mul_run (f : Bool) (st : St) (hC : st.C = 0) (hT : st.T = 0) (hZ : st.Z = 0)
    (hbd : st.Bd B) (hb : st.P * (if f then st.P else st.a) ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.cp (.mulF f) 0), st.toV, none)
      (some (mvExit (.mulT f)), St.toV { st with P := st.P * (if f then st.P else st.a) },
        none) := by
  set F := if f then st.P else st.a with hF
  have hFB : F ≤ B := by
    simp only [St.Bd] at hbd; rw [hF]; split <;> omega
  have hFs : st.toV (cpSrc (.mulF f)) = F := by cases f <;> rfl
  refine (cp_run (.mulF f) st hbd hZ (by rw [hFs]; regs [cpDst]; omega)).trans ?_
  rw [hFs]
  regs [cpDst, cpExit]
  have hbd1 : St.Bd B { st with C := st.C + F } := by simp only [St.Bd] at hbd ⊢; omega
  refine (mulL_run f F { st with C := st.C + F } (by show st.C + F = F; omega) hZ hbd1
    (by show st.T + F * st.P ≤ B; rw [hT, mul_comm]; omega)).trans ?_
  have hbd2 : St.Bd B { st with C := 0, T := st.T + F * st.P } := by
    simp only [St.Bd] at hbd ⊢; rw [mul_comm]; omega
  refine step_of hbd2 ?_
  regs [astep, A]
  have hbd3 : St.Bd B { st with C := 0, T := st.T + F * st.P, P := 0 } := by
    simp only [St.Bd] at hbd ⊢; rw [mul_comm]; omega
  refine reach_of_eq (mv_run (.mulT f) _ hbd3 (by regs [mvDst, mvSrc]; rw [mul_comm]; omega))
    ?_
  regs [mvDst, mvSrc]
  congr 3; ext <;> simp [hC, hT, mul_comm]

/-! ## The stack -/

/-- **Pushing `V`**: from `cp (push false)` with `C = T = Z = 0`, the machine shifts `SE`
left by `w` digits and adds `V` (clearing `V`), doubles `SP`, and reaches `mv descM`.

**Proof sketch.** Copy `w` into `C` (`cp_run`), shift `SE` (`sh_run`), move `V` into `SE`
(`mv_run`), move `SP` doubled into `T` and back (`dm_run`, `mv_run`). -/
theorem pushV_run (st : St) (hC : st.C = 0) (hT : st.T = 0) (hZ : st.Z = 0) (hbd : st.Bd B)
    (hSE : st.SE * 2 ^ st.w + st.V ≤ B) (hSP : 2 * st.SP ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.cp (.push false) 0), st.toV, none)
      (some (.mv .descM 0),
        St.toV { st with SE := st.SE * 2 ^ st.w + st.V, V := 0, SP := 2 * st.SP }, none) := by
  have hle : st.SE ≤ st.SE * 2 ^ st.w := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  simp only [St.Bd] at hbd
  refine (cp_run (.push false) st (by simp only [St.Bd]; omega) hZ
    (by regs [cpDst, cpSrc]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit, hC, zero_add]
  refine (sh_run (.push false) { st with C := st.w } (by simp only [St.Bd]; omega) hZ
    (by regs [shReg]; omega)).trans ?_
  regs [shReg, shExit]
  refine (mv_run (.pushX false) { st with C := 0, SE := st.SE * 2 ^ st.w }
    (by simp only [St.Bd]; omega)
    (by regs [mvDst, mvSrc, Bool.false_eq_true, if_false]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, Bool.false_eq_true, if_false]
  refine (dm_run false { st with C := 0, SE := st.SE * 2 ^ st.w + st.V, V := 0 }
    (by simp only [St.Bd]; omega) (by dsimp only; omega)).trans ?_
  refine reach_of_eq (mv_run (.pushSP false)
    { st with C := 0, SE := st.SE * 2 ^ st.w + st.V, V := 0, SP := 0, T := st.T + 2 * st.SP }
    (by simp only [St.Bd]; omega) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, Bool.false_eq_true, if_false]
  congr 3; ext <;> simp [hT]

/-- **Pushing `U`**: from `cp (push true)` with `C = T = Z = 0`, the machine shifts `SE`
left by `w` digits and adds `U` (clearing `U`), doubles `SP`, and reaches `pushInc`.

**Proof sketch.** As `pushV_run`, moving `U` instead of `V`. -/
theorem pushU_run (st : St) (hC : st.C = 0) (hT : st.T = 0) (hZ : st.Z = 0) (hbd : st.Bd B)
    (hSE : st.SE * 2 ^ st.w + st.U ≤ B) (hSP : 2 * st.SP ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.cp (.push true) 0), st.toV, none)
      (some .pushInc,
        St.toV { st with SE := st.SE * 2 ^ st.w + st.U, U := 0, SP := 2 * st.SP }, none) := by
  have hle : st.SE ≤ st.SE * 2 ^ st.w := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  simp only [St.Bd] at hbd
  refine (cp_run (.push true) st (by simp only [St.Bd]; omega) hZ
    (by regs [cpDst, cpSrc]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit, hC, zero_add]
  refine (sh_run (.push true) { st with C := st.w } (by simp only [St.Bd]; omega) hZ
    (by regs [shReg]; omega)).trans ?_
  regs [shReg, shExit]
  refine (mv_run (.pushX true) { st with C := 0, SE := st.SE * 2 ^ st.w }
    (by simp only [St.Bd]; omega) (by regs [mvDst, mvSrc, if_true]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, if_true]
  refine (dm_run true { st with C := 0, SE := st.SE * 2 ^ st.w + st.U, U := 0 }
    (by simp only [St.Bd]; omega) (by dsimp only; omega)).trans ?_
  refine reach_of_eq (mv_run (.pushSP true)
    { st with C := 0, SE := st.SE * 2 ^ st.w + st.U, U := 0, SP := 0, T := st.T + 2 * st.SP }
    (by simp only [St.Bd]; omega) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, if_true]
  congr 3; ext <;> simp [hT]

/-- **Popping a digit**: from `cp (popS b)` with `C = T = Z = Q = E = 0` and
`SE = q · 2 ^ w + e`, `e < 2 ^ w`, the machine sets `SE := q`, `E := e` and reaches `incI b`.

**Proof sketch.** `T := SE`, `C := w`, `T := T / 2 ^ C = q` (`hv_run`), `Q := T`, `C := w`,
`Q := Q · 2 ^ C` (`sh_run`), `SE := SE - Q = e` (`sb_run`), then move `SE` into `E` and
`T` into `SE` (`mv_run`). -/
theorem pop_run (b : Bool) (st : St) (q e : ℕ) (hC : st.C = 0) (hT : st.T = 0) (hZ : st.Z = 0)
    (hQ : st.Q = 0) (hE : st.E = 0) (hbd : st.Bd B) (hSE : st.SE = q * 2 ^ st.w + e)
    (he : e < 2 ^ st.w) :
    AReach (A E) orc x (GuardLe (A E) x B) (some (.cp (.popS b) 0), st.toV, none)
      (some (.incI b), St.toV { st with SE := q, E := e }, none) := by
  have hdiv : st.SE / 2 ^ st.w = q := by
    rw [hSE, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt he, zero_add]
  have hq : q ≤ st.SE := by rw [← hdiv]; exact Nat.div_le_self _ _
  have hq2 : q * 2 ^ st.w ≤ st.SE := by omega
  simp only [St.Bd] at hbd
  refine (cp_run (.popS b) st (by simp only [St.Bd]; omega) hZ
    (by regs [cpDst, cpSrc]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit, hT, zero_add]
  refine (cp_run (.popW1 b) { st with T := st.SE } (by simp only [St.Bd]; omega) hZ
    (by regs [cpDst, cpSrc]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit, hC, zero_add]
  refine (hv_run b { st with T := st.SE, C := st.w } (by simp only [St.Bd]; omega)).trans ?_
  dsimp only
  rw [hdiv]
  refine (cp_run (.popT b) { st with T := q, C := 0 } (by simp only [St.Bd]; omega) hZ
    (by regs [cpDst, cpSrc]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit, hQ, zero_add]
  refine (cp_run (.popW2 b) { st with T := q, C := 0, Q := q } (by simp only [St.Bd]; omega) hZ
    (by regs [cpDst, cpSrc]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit, zero_add]
  refine (sh_run (.pop b) { st with T := q, C := st.w, Q := q } (by simp only [St.Bd]; omega) hZ
    (by regs [shReg]; omega)).trans ?_
  regs [shReg, shExit]
  refine (sb_run b { st with T := q, C := 0, Q := q * 2 ^ st.w }
    (by simp only [St.Bd]; omega)).trans ?_
  dsimp only
  have hrem : st.SE - q * 2 ^ st.w = e := by omega
  rw [hrem]
  refine (mv_run (.popE b) { st with T := q, C := 0, Q := 0, SE := e }
    (by simp only [St.Bd]; omega) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, hE, zero_add]
  refine reach_of_eq (mv_run (.popT2 b) { st with T := q, C := 0, Q := 0, SE := 0, E := e }
    (by simp only [St.Bd]; omega) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit]
  congr 3; ext <;> simp

end SavitchARM

end Complexity.LogProg
