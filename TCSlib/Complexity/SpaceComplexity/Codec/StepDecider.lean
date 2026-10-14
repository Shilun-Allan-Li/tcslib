/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Layout2
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The step language is logspace

The codec machine `Complexity.Codec.CA` in mode `step` decides
`Complexity.Codec.stepLang N`: after the parse (`parse_run₂`), the layout of both code words
(`layout_run`, `layout2_run`), the position comparison (`le_phase`), the input-symbol read
(`insym_run`) and the validity scan of the first word (`vscan_run`), it reads the step data
into its control, moves the first word's input position by the action of each choice bit
and compares it with the second word's (`pm_run`), and runs the double sliding scan of the
two chunk regions (`s_run`). `Complexity.LogProg.arm_decides_poly` turns this into
membership in `L`.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
result of [AB09] by itself.

## Main definitions

* `Complexity.Codec.stepAns` — the answer of the step machine after the scan.

## Main results

* `Complexity.Codec.z_run`, `Complexity.Codec.step_tail` — the step tail.
* `Complexity.Codec.pm_run` — the position move and comparison of one choice bit.
* `Complexity.Codec.stepLang_mem` — the step language is in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool}

/-- A Boolean branch is the branch at the decision. -/
lemma ite_bool {α : Type} (p : Prop) [Decidable p] (f : Bool → α) :
    (if p then f true else f false) = f (decide p) := by
  by_cases h : p <;> simp [h]

/-- **The position move of one choice bit**: from `.pm I b f .start`, the machine compares
`rPos` moved by the action of `b` (clamped to `[0, rN1]`) with `rPos2`, restores `rPos`, and
continues with the verdict.

**Proof sketch.** By the move: no move compares directly; a right move compares directly at
the right end and otherwise increments, compares and decrements; a left move compares
directly at `0` and otherwise decrements, compares and increments. -/
theorem pm_run (y : List Bool) (I : SInfo N) (b f : Bool) (R : Regs) (hBd : R.Bd (bnd N y))
    (hN1 : 1 ≤ R.N1) (hle : R.Pos ≤ R.N1) (hbig : R.N1 + 1 ≤ bnd N y) :
    Reach N .step y (bnd N y) (.pm I b f .start) R.val
      (pmNext N I b f (decide (movePos (R.N1 - 1) R.Pos (aI N I b).inputTape = R.Pos2))) R.val := by
  set B := bnd N y
  have hv := hBd.val_le
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  cases hm : (aI N I b).inputTape with
  | zero =>
    refine Reach.single' (gd_of hv (by simp [PreS, CA, hm]; decide)) ?_
    simp only [astep, CA, hm, Regs.val_Pos, Regs.val_Pos2]
    rw [ite_bool]; rfl
  | pos =>
    by_cases hp : R.Pos = R.N1
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .eq) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm]; decide)) (by simp [astep, CA, hm, hp])
      refine r1.trans (Reach.single' (gd_of hv (by simp [PreS, CA]; decide)) ?_)
      simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
      rw [ite_bool]
      simp [movePos, show R.N1 - 1 + 1 = R.N1 by omega, hp]
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .inc) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm]; decide)) (by simp [astep, CA, hm, hp])
      have hv1 : ({R with Pos := R.Pos + 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
      have r2 : Reach N .step y B (.pm I b f .inc) R.val (.pm I b f .eq2)
          ({R with Pos := R.Pos + 1} : Regs).val :=
        Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA])
      have r3 : Reach N .step y B (.pm I b f .eq2) ({R with Pos := R.Pos + 1} : Regs).val
          (.pm I b f (.decR (decide (R.Pos + 1 = R.Pos2))))
          ({R with Pos := R.Pos + 1} : Regs).val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]; decide))
          (by simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
              by_cases h : R.Pos + 1 = R.Pos2 <;> simp [h])
      have r4 : Reach N .step y B (.pm I b f (.decR (decide (R.Pos + 1 = R.Pos2))))
          ({R with Pos := R.Pos + 1} : Regs).val (pmNext N I b f (decide (R.Pos + 1 = R.Pos2)))
          R.val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA])
      refine (r1.trans (r2.trans (r3.trans r4))).cast rfl |> fun h => ?_
      have : movePos (R.N1 - 1) R.Pos .pos = R.Pos + 1 := by
        simp [movePos, show R.N1 - 1 + 1 = R.N1 by omega, hp]
      rw [this]
      exact h
  | neg =>
    by_cases hp : R.Pos = 0
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .eq) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm])) (by simp [astep, CA, hm, hp])
      refine r1.trans (Reach.single' (gd_of hv (by simp [PreS, CA]; decide)) ?_)
      simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
      rw [ite_bool]
      simp [movePos, hp]
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .decN) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm])) (by simp [astep, CA, hm, hp])
      have hv1 : ({R with Pos := R.Pos - 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
      have r2 : Reach N .step y B (.pm I b f .decN) R.val (.pm I b f .eq3)
          ({R with Pos := R.Pos - 1} : Regs).val :=
        Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA])
      have r3 : Reach N .step y B (.pm I b f .eq3) ({R with Pos := R.Pos - 1} : Regs).val
          (.pm I b f (.incR (decide (R.Pos - 1 = R.Pos2))))
          ({R with Pos := R.Pos - 1} : Regs).val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]; decide))
          (by simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
              by_cases h : R.Pos - 1 = R.Pos2 <;> simp [h])
      have r4 : Reach N .step y B (.pm I b f (.incR (decide (R.Pos - 1 = R.Pos2))))
          ({R with Pos := R.Pos - 1} : Regs).val (pmNext N I b f (decide (R.Pos - 1 = R.Pos2)))
          R.val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
          (by simp [astep, CA, show R.Pos - 1 + 1 = R.Pos by omega])
      have : movePos (R.N1 - 1) R.Pos .neg = R.Pos - 1 := rfl
      rw [this]
      exact r1.trans (r2.trans (r3.trans r4))

/-- **Reading the step data into the control**: the code of the input symbol in `rZ` becomes
the second component of the step data.

**Proof sketch.** A zero test, a decrement and a second zero test on `rZ` distinguish the
three codes. -/
theorem z_run (y x : List Bool) (σ : VSt N) (R : Regs) (hBd : R.Bd (bnd N y)) (p : ℕ)
    (hZ : R.Z = zcode (inpOf x p)) :
    ∃ z, z ≤ 2 ∧ Reach N .step y (bnd N y) (.zA σ) R.val (.pm (σ, inpOf x p) false false .start)
      ({R with Z := z} : Regs).val := by
  have hv := hBd.val_le
  cases hin : inpOf x p with
  | none =>
    rw [hin] at hZ
    simp only [zcode] at hZ
    have hR : ({R with Z := 0} : Regs) = R := by cases R; simp_all
    refine ⟨0, by omega, ?_⟩
    rw [hR]
    exact Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA, hZ])
  | some c =>
    rw [hin] at hZ
    have r1 : Reach N .step y (bnd N y) (.zA σ) R.val (.zB σ) R.val :=
      Reach.single' (gd_of hv (by simp [PreS, CA]))
        (by cases c <;> simp [astep, CA, hZ, zcode])
    have hv1 : ({R with Z := R.Z - 1} : Regs).Bd (bnd N y) := by
      have := hBd; simp only [Regs.Bd] at this ⊢; omega
    have r2 : Reach N .step y (bnd N y) (.zB σ) R.val (.zC σ) ({R with Z := R.Z - 1} : Regs).val :=
      Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA])
    refine ⟨R.Z - 1, by cases c <;> simp [zcode] at hZ <;> omega, r1.trans (r2.trans ?_)⟩
    exact Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
      (by cases c <;> simp [astep, CA, hZ, zcode])

/-- The answer of the step machine after the validity scan, from the scan state `st`, the
input positions `p`, `p'`, and the two chunk regions `u`, `u'`. -/
noncomputable def stepAns (x : List Bool) (st : VSt N) (p p' : ℕ) (u u' : List Bool) : Bool :=
  decide (VAcc N st) &&
    ((decide (movePos x.length p (aI N (st, inpOf x p) false).inputTape = p') &&
        sDone N (Gs N (st, inpOf x p) false)
          (sScan N (Gs N (st, inpOf x p) false) (Gs N (st, inpOf x p) true) u u').1) ||
      (decide (movePos x.length p (aI N (st, inpOf x p) true).inputTape = p') &&
        sDone N (Gs N (st, inpOf x p) true)
          (sScan N (Gs N (st, inpOf x p) false) (Gs N (st, inpOf x p) true) u u').2))

/-- **The tail of the step mode**: after the validity scan of the first word, read the step
data, compare the positions for both choice bits (`pm_run`), run the double sliding scan of
the two chunk regions (`s_run`), and answer `stepAns`.

**Proof sketch.** A branch on the scan verdict, `z_run`, two `pm_run`s, `s_run` with the
letters of both words at stride two (`getD_w`, `getD_w2`), and the final `ret`. -/
theorem step_tail (y x w w' rest : List Bool)
    (hy : y = pairEncode x (pairEncode w (pairEncode w' rest))) (s : ℕ) (st : VAd N) (R : Regs)
    (hBd : R.Bd (bnd N y)) (hN1 : R.N1 = x.length + 1) (hPos : R.Pos ≤ x.length + 1)
    (hZ : R.Z = zcode (inpOf x R.Pos)) (hQ3 : R.Q3 = 2 * x.length + 2)
    (hQ4 : R.Q4 = 2 * x.length + 2 * w.length + 4)
    (hE : R.E = 2 * x.length + 2 + 4 * W N * s + 2 * W N)
    (hw : W N * (2 * s + 1) ≤ w.length) (hw' : W N * (2 * s + 1) ≤ w'.length)
    (hs : s ≤ 2 * y.length) :
    AHalt (CA N .step) orc y (GuardLe (CA N .step) y (bnd N y)) (some (.vDone st), R.val, none)
      (stepAns x st.1 R.Pos R.Pos2 (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1)))) := by
  set B := bnd N y
  have hv := hBd.val_le
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hyl : y.length = 2 * x.length + 2 * w.length + 2 * w'.length + 6 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hret : ∀ (l : Lab N) (v : Fin 21 → ℕ) (b : Bool), (∀ r, v r ≤ B) →
      CA N .step l = .ret b →
        AHalt (CA N .step) orc y (GuardLe (CA N .step) y B) (some l, v, none) b :=
    fun l v b hv h => AHalt.ret h ⟨by simp [PreS, h], hv⟩
  by_cases hacc : VAcc N st.1
  swap
  · have : stepAns x st.1 R.Pos R.Pos2 (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1)))
        = false := by simp [stepAns, hacc]
    rw [this]
    have r1 : Reach N .step y B (.vDone st) R.val .rej R.val :=
      Reach.single' (gd_of hv (by simp [PreS, CA, goto])) (by simp [astep, CA, goto, hacc])
    exact AReach.halt r1 (hret _ _ _ hv rfl)
  have r1 : Reach N .step y B (.vDone st) R.val (.zA st.1) R.val :=
    Reach.single' (gd_of hv (by simp [PreS, CA, goto])) (by simp [astep, CA, goto, hacc])
  obtain ⟨z, hz, r2⟩ := z_run (N := N) y x st.1 R hBd R.Pos hZ
  set I : SInfo N := (st.1, inpOf x R.Pos)
  set R2 : Regs := {R with Z := z}
  have hR2 : R2.Bd B := by simp only [R2, Regs.Bd]; omega
  have r3 := pm_run (N := N) y I false false R2 hR2 (by simp [R2, hN1]) (by simp [R2, hN1, hPos])
    (by simp [R2, hN1]; omega)
  set f₀ := decide (movePos (R2.N1 - 1) R2.Pos (aI N I false).inputTape = R2.Pos2)
  have r4 := pm_run (N := N) y I true f₀ R2 hR2 (by simp [R2, hN1]) (by simp [R2, hN1, hPos])
    (by simp [R2, hN1]; omega)
  set f₁ := decide (movePos (R2.N1 - 1) R2.Pos (aI N I true).inputTape = R2.Pos2)
  simp only [pmNext, Bool.false_eq_true, ↓reduceIte] at r3 r4
  set u := w.take (W N * (2 * s + 1))
  set u' := w'.take (W N * (2 * s + 1))
  have hu : u.length = W N * (2 * s + 1) := by simp only [u, List.length_take]; omega
  have hu' : u'.length = W N * (2 * s + 1) := by simp only [u', List.length_take]; omega
  have r5 := s_run (N := N) (mode := .step) y B I f₀ f₁ u u' (by rw [hu, hu']) (sAd0 N) R2.val
    hR2.val_le (by simp [R2, hu, hE, hQ3]; ring)
    (by simp [R2, hu, hQ4]; have : 2 * (W N * (2 * s + 1)) = 4 * W N * s + 2 * W N := by ring
        omega)
    (fun i hi => by
      rw [hu] at hi
      simp only [R2, Regs.val_Q3, hQ3]
      rw [hy, getD_w _ _ _ _ (by omega)]
      simp only [u, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi])
    (fun i hi => by
      rw [hu] at hi
      simp only [R2, Regs.val_Q4, hQ4]
      rw [hy, getD_w2 _ _ _ _ _ (by omega)]
      simp only [u', List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi])
  set R5 : Regs := {R2 with Q3 := R2.Q3 + 2 * u.length, Q4 := R2.Q4 + 2 * u.length}
  have hR5 : R5.Bd B := by
    simp only [R5, R2, Regs.Bd, hu]
    have : 2 * (W N * (2 * s + 1)) = 4 * W N * s + 2 * W N := by ring
    omega
  have r5' : Reach N .step y B (.sTest I f₀ f₁ (sAd0 N)) R2.val
      (.sFin I f₀ f₁ ((List.zip u u').foldl (δS N I) (sAd0 N))) R5.val :=
    Reach.cast r5 (by simp [R5])
  have hans : stepAns x st.1 R.Pos R.Pos2 u u' =
      ((f₀ && sDone N (Gs N I false) ((List.zip u u').foldl (δS N I) (sAd0 N)).1.1) ||
        (f₁ && sDone N (Gs N I true) ((List.zip u u').foldl (δS N I) (sAd0 N)).1.2)) := by
    simp only [stepAns, hacc, decide_true, Bool.true_and, f₀, f₁, R2, hN1,
      Nat.add_sub_cancel, I]
    rfl
  rw [hans]
  exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans r5')))) (hret _ _ _ hR5.val_le rfl)

/-- The answer of the step machine is the step check, on inputs passing the pre-scan
checks of both words. -/
lemma stepAns_iff (x w w' : List Bool) (s : ℕ) (hpre : PreChk N x.length s w)
    (hlen' : w'.length = W N * (2 * s + 1) + wP x.length + 1)
    (hterm' : w'.getD (W N * (2 * s + 1) + wP x.length) false = true) :
    stepAns x (vScan N (w.take (W N * (2 * s + 1))))
        (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))
        (bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)))
        (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))) = true ↔
      StepChk N x s w w' := by
  unfold StepChk stepAns
  rw [validChk_iff_pre]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hacc, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨⟨hpre, hacc⟩, hlen', hterm', false, h1.symm, h2⟩
    · exact ⟨⟨hpre, hacc⟩, hlen', hterm', true, h1.symm, h2⟩
  · rintro ⟨⟨-, hacc⟩, -, -, b, h1, h2⟩
    refine ⟨hacc, ?_⟩
    cases b
    · exact Or.inl ⟨h1.symm, h2⟩
    · exact Or.inr ⟨h1.symm, h2⟩

/-- Members of the step language are well shaped. -/
lemma shape2_of_code {y x : List Bool} {c c' s : ℕ}
    (hy : y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))))
    (C : Cfg N.k Bool N.State x) (hc : cfgCode s C = c) :
    Shape2 y x (Nat.bits c) (Nat.bits c') s := by
  refine ⟨hy, width_of_code s C y ?_⟩
  rw [hy, ← hc, bits_cfgCode]
  simp [length_pairEncode]; omega

/-- **The step language is logspace** (`Complexity.Codec.stepLang`).

**Proof sketch.** `arm_decides_poly` with the codec machine in mode `step`: the phases
`parse_run₂`, `layout_run`, `le_phase`, `layout2_run`, `insym_run`, `vscan_run`,
`step_tail` answer `stepAns`, which on well-shaped inputs passing the pre-scan checks is the
step check (`stepAns_iff`), i.e. membership (`stepLang_iff`); every rejection on the way
falsifies the step check or the shape (`shape2_of_code`). -/
theorem stepLang_mem : stepLang N ∈ LOGSPACE := by
  refine arm_decides_poly (CA N .step) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  set B := bnd N y
  -- non-members: no shape, or a failed check
  have hnon : (∀ x w w' s, Shape2 y x w w' s → ¬ StepChk N x s w w') →
      MultiTapeTM.indicator (stepLang N : Set (List Bool)) y = false := by
    intro hfail
    rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
    · rfl
    obtain ⟨x, c, c', s, hy, C, hC, hc, C', hstep, hC', hc'⟩ := h
    have hsh := shape2_of_code (c' := c') hy C hc
    exact hfail x _ _ s hsh ((stepLang_iff N x (Nat.bits c) (Nat.bits c') s).mp
      ⟨x, c, c', s, rfl, C, hC, hc, C', hstep, hC', hc'⟩)
  rcases parse_run₂ (N := N) y with ⟨x, w, w', s, q1, cap, ⟨hy, hwid⟩, hq1, hcap, r1⟩ |
      ⟨hno, hhalt⟩
  swap
  · rw [hnon (fun x w w' s h => absurd ⟨x, w, w', s, h⟩ hno)]
    exact hhalt
  have hyl : y.length = 2 * x.length + 2 * w.length + 2 * w'.length + 6 + (Nat.bits s).length := by
    rw [hy, length_pairEncode, length_pairEncode, length_pairEncode]; ring
  have hs := s_le_of_width y s (by omega) hwid
  have hbig := bnd_ge (N := N) y s hs
  have hlink : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
  have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
  have huniq : ∀ x₁ w₁ w₁' s₁, Shape2 y x₁ w₁ w₁' s₁ → x₁ = x ∧ w₁ = w ∧ w₁' = w' ∧ s₁ = s := by
    rintro x₁ w₁ w₁' s₁ ⟨hy₁, -⟩
    rw [hy] at hy₁
    obtain ⟨h1, h2⟩ := pairEncode_inj hy₁
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    obtain ⟨h5, h6⟩ := pairEncode_inj h4
    exact ⟨h1.symm, h3.symm, h5.symm, (bits_injective h6).symm⟩
  set R1 : Regs := { L := y.length, P := 2 * x.length + 2 * w.length + 2 * w'.length + 6,
                     A := 2 * x.length + 2, B := 2 * x.length + 2 * w.length + 4, Q1 := q1,
                     Cap := cap, Q2 := 2 * x.length + 2 * w.length + 2 * w'.length + 6, S := s }
  have hR1 : R1.Bd B := by simp only [R1, Regs.Bd]; omega
  rcases layout_run (N := N) (mode := .step) y x w (pairEncode w' (Nat.bits s)) hy R1 s hR1 rfl rfl
    rfl hs rfl rfl rfl rfl rfl rfl rfl (by simp [R1]) with ⟨hlen, hterm, r2⟩ | ⟨hbad, hhalt⟩
  swap
  · rw [hnon (fun x₁ w₁ w₁' s₁ hsh hchk => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq x₁ w₁ w₁' s₁ hsh
      exact hbad ⟨hchk.1.1, hchk.1.2.2.2⟩)]
    exact AReach.halt r1 hhalt
  set pos := bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length))
  set R2 := layR N R1 x.length s pos
  have hwP := wP_le x.length
  have hpos_lt : pos < 2 * (x.length + 1) := by
    have h1 := bitsVal_lt_two_pow ((w.drop (W N * (2 * s + 1))).take (wP x.length))
    have h2 : 2 ^ ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
        2 * (x.length + 1) := by
      rw [show ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
        simp; omega]
      exact two_pow_bits_le _ (by omega)
    omega
  have hR2 : R2.Bd B := by simp only [R2, R1, layR, Regs.Bd]; omega
  obtain ⟨hle, hgt⟩ := le_phase (N := N) (mode := .step) y R2 hR2 (by simp [R2, R1, layR])
  by_cases hp : pos ≤ x.length + 1
  swap
  · rw [hnon (fun x₁ w₁ w₁' s₁ hsh hchk => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq x₁ w₁ w₁' s₁ hsh
      exact hp hchk.1.2.2.1)]
    exact AReach.halt (r1.trans r2) (hgt (by simpa [R2, R1, layR] using hp))
  have r3 := hle (by simpa [R2, R1, layR] using hp)
  simp only [↓reduceIte] at r3
  rcases layout2_run (N := N) y x w w' (Nat.bits s) hy R2 s hR2 (by simp [R2, R1, layR])
    (by simp [R2, R1, layR]) (by simp [R2, R1, layR]) hs (by simp [R2, layR])
    (by simp [R2, R1, layR]) (by simp [R2, R1, layR]) (by simp [R2, R1, layR])
    (by simp [R2, R1, layR]) with ⟨hlen', hterm', r4⟩ | ⟨hbad', hhalt'⟩
  swap
  · rw [hnon (fun x₁ w₁ w₁' s₁ hsh hchk => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq x₁ w₁ w₁' s₁ hsh
      exact hbad' ⟨hchk.2.1, hchk.2.2.1⟩)]
    exact AReach.halt (r1.trans (r2.trans r3)) hhalt'
  set pos' := bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length))
  set R3 := lay2R N R2 (2 * x.length + 2 * w.length + 4) s (wP x.length) pos'
  have hpos'_lt : pos' < 2 * (x.length + 1) := by
    have h1 := bitsVal_lt_two_pow ((w'.drop (W N * (2 * s + 1))).take (wP x.length))
    have h2 : 2 ^ ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
        2 * (x.length + 1) := by
      rw [show ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
        simp; omega]
      exact two_pow_bits_le _ (by omega)
    omega
  have hR3 : R3.Bd B := by simp only [R3, R2, R1, lay2R, layR, Regs.Bd]; omega
  obtain ⟨u, hu, r5⟩ := insym_run (N := N) y x (pairEncode w (pairEncode w' (Nat.bits s))) hy R3 hR3
    (by simp [R3, R2, R1, lay2R, layR]; omega) (by simp [R3, R2, R1, lay2R, layR])
    (by simp [R3, lay2R]) (by simp [R3, R2, R1, lay2R, layR]) (by simp [R3, R2, R1, lay2R, layR])
    (by simp [R3, R2, R1, lay2R, layR])
  set R4 : Regs := {R3 with Z := zcode (inpOf x R3.Pos), U := u, Q3 := R3.A, Q4 := R3.B}
  have hR4 : R4.Bd B := by
    simp only [R4, R3, R2, R1, lay2R, layR, Regs.Bd]
    have : zcode (inpOf x pos) ≤ 2 := by
      unfold zcode; split <;> omega
    omega
  obtain ⟨st, hst, r6⟩ := vscan_run (N := N) (mode := .step) y x w (pairEncode w' (Nat.bits s)) hy
    R4 s hR4 (by simp [R4, R3, R2, R1, lay2R, layR]) (by simp [R4, R3, R2, lay2R, layR])
    (by omega)
  set R5 : Regs := {R4 with Q1 := R4.E, Q2 := R4.E}
  have hR5 : R5.Bd B := by
    simp only [R5, R4, R3, R2, R1, lay2R, layR, Regs.Bd]
    have : zcode (inpOf x pos) ≤ 2 := by
      unfold zcode; split <;> omega
    omega
  have tail := step_tail (N := N) y x w w' (Nat.bits s) hy s st R5 hR5
    (by simp [R5, R4, R3, R2, R1, lay2R, layR]) (by simp [R5, R4, R3, R2, R1, lay2R, layR]; omega)
    (by simp [R5, R4, R3, R2, R1, lay2R, layR]) (by simp [R5, R4, R3, R2, R1, lay2R, layR])
    (by simp [R5, R4, R3, R2, R1, lay2R, layR]) (by simp [R5, R4, R3, R2, lay2R, layR])
    (by omega) (by omega) hs
  have hPosR5 : R5.Pos = pos := by simp [R5, R4, R3, R2, R1, lay2R, layR]
  have hPos2R5 : R5.Pos2 = pos' := by simp [R5, R4, R3, R2, R1, lay2R, layR]
  rw [hst, hPosR5, hPos2R5] at tail
  have hind : MultiTapeTM.indicator (stepLang N : Set (List Bool)) y =
      stepAns x (vScan N (w.take (W N * (2 * s + 1)))) pos pos'
        (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))) := by
    rw [indicator_eq_decide]
    have key := stepAns_iff (N := N) x w w' s ⟨hlen, hterm, hp⟩ hlen' hterm'
    rw [hy, stepLang_iff]
    cases h : stepAns x (vScan N (w.take (W N * (2 * s + 1)))) pos pos'
        (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1)))
    · simp only [decide_eq_false_iff_not]
      intro hc; rw [← key] at hc; rw [hc] at h; exact Bool.noConfusion h
    · simp only [decide_eq_true_eq]
      exact key.mp h
  rw [hind]
  exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))) tail

end Complexity.Codec
