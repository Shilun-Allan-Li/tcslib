/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The walks of the window-growing counting machine

The walk subroutine of `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2: the membership
certificate is a guessed path]: from `w0 b` it guesses a start code `g < K`,
checks it is initial, and walks, guessing each next code below `K` and checking the step
pair, until it meets the target (`v` at the outer site, `u` at the inner one) or has made as
many steps as the bound; on success it clears `g`, `cur`, `stp` and continues at the exit.

The statements here are **guarded**: the semantics at the exit is only required when the
walk succeeded (the target is in the ball, `Complexity.LogProg.ISCount.Mem`). Exits reached
with an impossible register file need no semantics, which is what lets the radius loop of
`igA` require its continuation only at the correct counts.

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main results

* `Complexity.LogProg.ISGen.gwalk_loop` — the walk loop.
* `Complexity.LogProg.ISGen.gwalk_spec` — the walk subroutine.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing ISCount ISTac

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- **The walk loop** (guarded): at `wl b`, with the current code `cur < K` after `stp` steps
out of the bound `L`, some branch accepts iff the target is reachable from `cur` within
`L - stp` steps through codes below `K` and the continuation at the exit accepts (with the
scratch registers cleared); every branch terminates. The continuation is only needed when
the target is so reachable.

**Proof sketch.** Induction on `L - stp`: at the target exit (the walk of length `0`
witnesses reachability); out of steps reject; otherwise guess `g < K` (`nsem_guess`), reject
unless `(cur, g)` is a step pair, copy `g` into `cur` (`nsem_copy`), count the step, and
recur with the guard pulled back along the step. -/
theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B)
    (hcur : σ.cur < σ.K) (hstp : σ.stp ≤ σ.wb b)
    (hQ : WalkLe (RelO orc x σ.s) σ.K (σ.wb b - σ.stp) σ.cur (σ.wt b) →
      IG (E := E) orc x B (gwX b) { σ with cur := 0, stp := 0, g := 0 } Q) :
    IG (E := E) orc x B (.wl b) σ
      (WalkLe (RelO orc x σ.s) σ.K (σ.wb b - σ.stp) σ.cur (σ.wt b) ∧ Q) := by
  suffices H : ∀ dd (σ : St), σ.wb b - σ.stp = dd → σ.Bd B → σ.K + 1 ≤ B → σ.cur < σ.K →
      σ.stp ≤ σ.wb b →
      (WalkLe (RelO orc x σ.s) σ.K dd σ.cur (σ.wt b) →
        IG (E := E) orc x B (gwX b) { σ with cur := 0, stp := 0, g := 0 } Q) →
      IG (E := E) orc x B (.wl b) σ (WalkLe (RelO orc x σ.s) σ.K dd σ.cur (σ.wt b) ∧ Q) by
    exact H _ σ rfl hσ hK hcur hstp hQ
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ hK hcur hstp hQ
    by_cases he : σ.cur = σ.wt b
    · refine (NSem.jeq_pos (P := Q) rfl (St.greg hσ _ _)
        (by simp only [St.toV_cur, toV_wT]; exact he) ?_).congr ?_
      · refine NSem.clr rfl (St.greg hσ _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        exact hQ he
      · simp only [WalkLe, he, true_and]
    · have hL : σ.stp = σ.wb b := by omega
      refine (NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he)
        (NSem.jeq_pos rfl (St.greg hσ _ _) (by simp only [St.toV_stp, toV_wB]; exact hL)
          (NSem.ret rfl (St.greg hσ _ _)))).congr ?_
      simp only [WalkLe, he, Bool.false_eq_true, false_and]
  | succ dd ih =>
    intro σ hd hσ hK hcur hstp hQ
    by_cases he : σ.cur = σ.wt b
    · refine (NSem.jeq_pos (P := Q) rfl (St.greg hσ _ _)
        (by simp only [St.toV_cur, toV_wT]; exact he) ?_).congr ?_
      · refine NSem.clr rfl (St.greg hσ _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        exact hQ (Or.inl he)
      · simp only [WalkLe, he, true_or, true_and]
    have hbd : σ.wb b ≤ B := by simp only [St.wb, St.Bd] at hσ ⊢; cases b <;> simp <;> omega
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he) ?_
    have hL : σ.stp ≠ σ.wb b := by omega
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_stp, toV_wB]; exact hL) ?_
    refine NSem.clr rfl (St.greg hσ _ _) ?_
    isr
    refine (nsem_guess (igA E) orc x B rg rK (by decide) (.gt b true) (.gc b true) (.gm b true)
      (.gxS b) .rej rfl rfl rfl rfl
      (fun j => RelO orc x σ.s σ.cur j ∧
        (WalkLe (RelO orc x σ.s) σ.K dd j (σ.wt b) ∧ Q)) _
      (St.greg (E := E) (by isb) none none) (by simp) (fun j hj1 hj2 => ?_)).congr ?_
    · simp only [St.toV_K] at hj2
      isr
      by_cases hr : RelO orc x σ.s σ.cur j
      · refine nsem_call₃_pos rfl (St.greg (by isb) _ _) (by isr; exact hr) ?_
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b true) (.wcb b true)
          (.wst b) rfl rfl _ _ (St.greg (E := E) (by isb) none none) (by simp) ?_
        isr
        refine NSem.inc rfl (St.greg (by isb) _ _) ?_
        isr
        refine (ih { σ with g := j, cur := j, stp := σ.stp + 1 }
          (by show St.wb b σ - (σ.stp + 1) = dd; omega)
          (by isb) hK (by simpa using hj2) (by show σ.stp + 1 ≤ St.wb b σ; omega)
          (fun hw => IG.of_eq (by ext <;> rfl)
            (hQ (Or.inr ⟨j, by simpa using hj2, hr, by simpa [St.wt] using hw⟩)))).congr ?_
        simp [St.wt, hr]
      · refine (nsem_call₃_neg rfl (St.greg (by isb) _ _)
          (by isr; simpa [SavitchARM.Rel] using hr)
          (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
        simp only [Bool.false_eq_true, false_iff, not_and]
        exact fun h => absurd h hr
    · simp only [St.toV_g, St.toV_K, WalkLe, he, false_or]
      constructor
      · rintro ⟨j, -, hj, h1, h2, hq⟩; exact ⟨⟨j, hj, h1, h2⟩, hq⟩
      · rintro ⟨⟨j, hj, h1, h2⟩, hq⟩; exact ⟨j, Nat.zero_le _, hj, h1, h2, hq⟩

/-- **The walk subroutine** (guarded) [AB09, §4.3.2: the membership certificate is a guessed
path]: from `w0 b`, some branch accepts iff the target is in the ball of radius the bound and
the continuation at the exit accepts with `g`, `cur`, `stp` cleared; every branch
terminates. The continuation is only needed when the target is in the ball.

**Proof sketch.** Guess the start code (`nsem_guess`), reject unless it is initial, copy it
into `cur` (`nsem_copy`), clear the step count, and run the walk loop (`gwalk_loop`); a
successful walk from an initial code witnesses membership in the ball, discharging the
guard. -/
theorem gwalk_spec (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B)
    (hQ : Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) (σ.wb b) (σ.wt b) →
      IG (E := E) orc x B (gwX b) { σ with cur := 0, stp := 0, g := 0 } Q) :
    IG (E := E) orc x B (.w0 b) σ
      (Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) (σ.wb b) (σ.wt b) ∧ Q) := by
  refine NSem.clr rfl (St.greg hσ _ _) ?_
  isr
  refine (nsem_guess (igA E) orc x B rg rK (by decide) (.gt b false) (.gc b false)
    (.gm b false) (.gxI b) .rej rfl rfl rfl rfl
    (fun j => InitO orc x σ.s j ∧ (WalkLe (RelO orc x σ.s) σ.K (σ.wb b) j (σ.wt b) ∧ Q)) _
    (St.greg (E := E) (by isb) none none) (by simp) (fun j hj1 hj2 => ?_)).congr ?_
  · simp only [St.toV_K] at hj2
    isr
    by_cases hi : InitO orc x σ.s j
    · refine nsem_call₂_pos rfl (St.greg (by isb) _ _) (by isr; exact hi) ?_
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b false) (.wcb b false)
        (.w2 b) rfl rfl _ _ (St.greg (E := E) (by isb) none none) (by simp) ?_
      isr
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      refine (gwalk_loop b Q { σ with g := j, cur := j, stp := 0 } (by isb) hK
        (by simpa using hj2) (Nat.zero_le _)
        (fun hw => IG.of_eq (by ext <;> rfl)
          (hQ ⟨j, by simpa using hj2, hi, by simpa [St.wb, St.wt] using hw⟩))).congr ?_
      exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
    · refine (nsem_call₂_neg rfl (St.greg (by isb) _ _)
        (by isr; simpa [SavitchARM.InitO] using hi)
        (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_and]
      exact fun h => absurd h hi
  · simp only [St.toV_g, St.toV_K, Mem]
    constructor
    · rintro ⟨j, -, hj, h1, h2, hq⟩; exact ⟨⟨j, hj, h1, h2⟩, hq⟩
    · rintro ⟨⟨j, hj, h1, h2⟩, hq⟩; exact ⟨j, Nat.zero_le _, hj, h1, h2, hq⟩

end ISGen

end Complexity.LogProg
