/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Layout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The one-code languages are logspace

The codec machine `Complexity.Codec.CA` in the modes `valid`, `accept`, `init` decides the
languages `Complexity.Codec.validLang N`, `acceptLang N`, `initLang N`: it parses
(`parse_run`), lays out the code word (`layout_run`), compares the input position
(`le_phase`), scans the chunk region (`vscan_run`), and answers from the scan state — for
the initial code after testing the input position and the head flag of the middle cell.
`Complexity.LogProg.arm_decides_poly` turns this into membership in `L`.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
result of [AB09] by itself.

## Main definitions

* `Complexity.Codec.PreChk` — the checks done before the scan.
* `Complexity.Codec.InitScan` — the scan-state part of the initial-code test.

## Main results

* `Complexity.Codec.one_run` — the common run of the one-code modes.
* `Complexity.Codec.init_tail` — the tail of the initial-code mode.
* `Complexity.Codec.validLang_mem`, `Complexity.Codec.acceptLang_mem`,
  `Complexity.Codec.initLang_mem` — the three languages are in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {mode : CMode}

/-! ## Members are well shaped -/

/-- A code at radius `s` is longer than `s`, so a well-formed input `⟨x, ⟨bits c, bits s⟩⟩`
with `c` a code passes the width check of its radius field. -/
lemma width_of_code {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) (y : List Bool)
    (hy : (cfgWord s C).length ≤ y.length) :
    (Nat.bits s).length ≤ (Nat.bits y.length).length := by
  apply length_bits_mono
  have := length_cfgWord s C
  have hW : 1 ≤ W N := by simp [W]
  have : 2 * s + 1 ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_left _ hW
  omega

/-- The input length is at least the code word's. -/
lemma cfgWord_le_length {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) (rest : List Bool) :
    (cfgWord s C).length ≤ (pairEncode x (pairEncode (cfgWord s C) rest)).length := by
  simp [length_pairEncode]; omega

/-- The register bound in the form of `arm_decides_poly`. -/
lemma gd_mono {y : List Bool} (a : AConf 21 (Lab N)) (h : GuardLe (CA N mode) y (bnd N y) a) :
    PreS (CA N mode) y a ∧ ∀ r, a.2.1 r ≤ (8 * W N + 8) * (y.length + 1) ^ 1 := by
  simpa [bnd] using h

/-- The empty register file is the zero valuation. -/
lemma val_empty : ({} : Regs).val = fun _ => 0 := by
  funext r; fin_cases r <;> rfl

/-- The radius of a well-shaped input is at most twice the input length. -/
lemma s_le_of_width (y : List Bool) (s : ℕ) (hy : 1 ≤ y.length)
    (h : (Nat.bits s).length ≤ (Nat.bits y.length).length) : s ≤ 2 * y.length := by
  have h1 := bitsVal_le_of_width (Nat.bits s) y.length hy h 0
  simpa [bitsVal_bits] using h1

/-! ## The common run of the one-code modes -/

variable (N) in
/-- The checks done before the scan: the length, the final letter, and the input position. -/
def PreChk (n s : ℕ) (w : List Bool) : Prop :=
  w.length = W N * (2 * s + 1) + wP n + 1 ∧ w.getD (W N * (2 * s + 1) + wP n) false = true ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP n)) ≤ n + 1

/-- The validity test is the pre-scan checks and the scan verdict. -/
lemma validChk_iff_pre (n s : ℕ) (w : List Bool) :
    ValidChk (N := N) n s w ↔ PreChk N n s w ∧ VAcc N (vScan N (w.take (W N * (2 * s + 1)))) := by
  unfold ValidChk PreChk
  tauto

/-- **The common run of the one-code modes**: on a well-shaped input passing the pre-scan
checks the machine reaches the end of the validity scan, with the scan state of the chunk
region and the layout in its registers; otherwise it rejects, and then no decomposition of
the input passes the pre-scan checks.

**Proof sketch.** `parse_run`, `layout_run`, `le_phase`, `vscan_run` in sequence; each
rejection is matched with the failed shape or check. -/
theorem one_run (hm : mode ≠ .step) (y : List Bool) :
    (∃ (x w : List Bool) (s : ℕ), Shape1 y x w s ∧ PreChk N x.length s w ∧
      ∃ (st : VAd N) (R : Regs), st.1 = vScan N (w.take (W N * (2 * s + 1))) ∧
        R.Bd (bnd N y) ∧ R.A = 2 * x.length + 2 ∧ R.S = s ∧ R.T = 0 ∧
        R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) ∧
        Reach N mode y (bnd N y) .lenScan ({} : Regs).val (.vDone st) R.val) ∨
    ((∀ x w s, Shape1 y x w s → ¬ PreChk N x.length s w) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y)) (some .lenScan, ({} : Regs).val, none)
        false) := by
  set B := bnd N y
  rcases parse_run (N := N) hm y with ⟨x, w, s, q1, cap, hsh, hq1, hcap, r1⟩ | ⟨hno, hhalt⟩
  · obtain ⟨hy, hwid⟩ := hsh
    have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hy, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hwid
    have hbig := bnd_ge (N := N) y s hs
    have hlink : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
    have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
    set R1 : Regs := { L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
                       Q1 := q1, Cap := cap, Q2 := 2 * x.length + 2 * w.length + 4, S := s }
    have hR1 : R1.Bd B := by simp only [R1, Regs.Bd]; omega
    -- uniqueness of the decomposition
    have huniq : ∀ x' w' s', Shape1 y x' w' s' → x' = x ∧ w' = w ∧ s' = s := by
      rintro x' w' s' ⟨hy', -⟩
      rw [hy] at hy'
      obtain ⟨h1, h2⟩ := pairEncode_inj hy'
      obtain ⟨h3, h4⟩ := pairEncode_inj h2
      exact ⟨h1.symm, h3.symm, (bits_injective h4).symm⟩
    rcases layout_run (N := N) (mode := mode) y x w (Nat.bits s) hy R1 s hR1 rfl rfl rfl hs rfl
      rfl rfl rfl rfl rfl rfl (by simp [R1, hm]) with ⟨hlen, hterm, r2⟩ | ⟨hbad, hhalt⟩
    · set pos := bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length))
      set R2 := layR N R1 x.length s pos
      have hpos_lt : pos < 2 * (x.length + 1) := by
        have h1 := bitsVal_lt_two_pow ((w.drop (W N * (2 * s + 1))).take (wP x.length))
        have h2 : 2 ^ ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
            2 * (x.length + 1) := by
          rw [show ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
            simp; omega]
          exact two_pow_bits_le _ (by omega)
        omega
      have hwP := wP_le x.length
      have hR2 : R2.Bd B := by simp only [R2, R1, layR, Regs.Bd]; omega
      obtain ⟨hle, hgt⟩ := le_phase (N := N) (mode := mode) y R2 hR2 (by simp [R2, R1, layR])
      by_cases hp : pos ≤ x.length + 1
      · left
        have r3 := hle (by simpa [R2, R1, layR] using hp)
        rw [if_neg hm] at r3
        obtain ⟨st, hst, r4⟩ := vscan_run (N := N) (mode := mode) y x w (Nat.bits s) hy R2 s hR2
          (by simp [R2, R1, layR]) (by simp [R2, layR]) (by omega)
        refine ⟨x, w, s, ⟨hy, hwid⟩, ⟨hlen, hterm, hp⟩, st, _, hst, ?_, ?_, ?_, ?_, ?_,
          r1.trans (r2.trans (r3.trans r4))⟩
        · simp only [R2, R1, layR, Regs.Bd]; omega
        · simp [R2, R1, layR]
        · simp [R2, R1, layR]
        · simp [R2, R1, layR]
        · simp [R2, layR, pos]
      · right
        refine ⟨fun x' w' s' hsh' hpre => ?_, AReach.halt (r1.trans r2) (hgt (by
          simpa [R2, R1, layR] using hp))⟩
        obtain ⟨rfl, rfl, rfl⟩ := huniq x' w' s' hsh'
        exact hp hpre.2.2
    · right
      refine ⟨fun x' w' s' hsh' hpre => ?_, AReach.halt r1 hhalt⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq x' w' s' hsh'
      exact hbad ⟨hpre.1, hpre.2.1⟩
  · right
    exact ⟨fun x w s h => absurd ⟨x, w, s, h⟩ hno, hhalt⟩

/-! ## Valid and accepting codes -/

/-- An indicator through a decidable characterization. -/
lemma indicator_eq_of_iff {L : Language Bool} {y : List Bool} {P : Prop} [Decidable P]
    (h : y ∈ L ↔ P) : MultiTapeTM.indicator (L : Set (List Bool)) y = decide P := by
  rw [indicator_eq_decide]
  exact decide_eq_decide.mpr h

/-- Members of the one-code languages are well shaped. -/
lemma shape_of_code {y x : List Bool} {c s : ℕ}
    (hy : y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)))
    (C : Cfg N.k Bool N.State x) (hc : cfgCode s C = c) : Shape1 y x (Nat.bits c) s := by
  refine ⟨hy, width_of_code s C y ?_⟩
  rw [hy, ← hc, bits_cfgCode]
  exact cfgWord_le_length s C _

/-- **Valid codes form a logspace language** (`Complexity.Codec.validLang`).

**Proof sketch.** `arm_decides_poly` with the codec machine in mode `valid`: on a well-shaped
input passing the pre-scan checks it answers the scan verdict, which is then membership
(`validLang_iff`, `validChk_iff_pre`); otherwise it rejects, and the input is no member
(members are well shaped, `shape_of_code`, and pass all checks). -/
theorem validLang_mem : validLang N ∈ LOGSPACE := by
  refine arm_decides_poly (CA N .valid) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  rcases one_run (N := N) (mode := .valid) (by decide) y with
    ⟨x, w, s, hsh, hpre, st, R, hst, hR, -, -, -, -, run⟩ | ⟨hfail, hhalt⟩
  · have hind : MultiTapeTM.indicator (validLang N : Set (List Bool)) y =
        decide (VAcc N st.1) := by
      apply indicator_eq_of_iff
      rw [hsh.1, validLang_iff, validChk_iff_pre, hst]
      exact ⟨fun h => h.2, fun h => ⟨hpre, h⟩⟩
    rw [hind]
    exact AReach.halt run (AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩)
  · have hind : MultiTapeTM.indicator (validLang N : Set (List Bool)) y = false := by
      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
      · rfl
      obtain ⟨x, c, s, hy, C, hC, hc⟩ := h
      have hsh := shape_of_code hy C hc
      have hv := (validLang_iff N x (Nat.bits c) s).mp ⟨x, c, s, rfl, C, hC, hc⟩
      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv).1
    rw [hind]
    exact hhalt

/-- **Accepting codes form a logspace language** (`Complexity.Codec.acceptLang`).

**Proof sketch.** As `validLang_mem`, answering the scan verdict together with the header
`(halted, accept)` (`acceptLang_iff`). -/
theorem acceptLang_mem : acceptLang N ∈ LOGSPACE := by
  refine arm_decides_poly (CA N .accept) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  rcases one_run (N := N) (mode := .accept) (by decide) y with
    ⟨x, w, s, hsh, hpre, st, R, hst, hR, -, -, -, -, run⟩ | ⟨hfail, hhalt⟩
  · have hind : MultiTapeTM.indicator (acceptLang N : Set (List Bool)) y =
        decide (VAcc N st.1 ∧ st.1.2.1 = some (none, 1)) := by
      apply indicator_eq_of_iff
      rw [hsh.1, acceptLang_iff, AcceptChk, validChk_iff_pre, hst]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hpre, h.1⟩, h.2⟩⟩
    rw [hind]
    exact AReach.halt run (AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩)
  · have hind : MultiTapeTM.indicator (acceptLang N : Set (List Bool)) y = false := by
      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
      · rfl
      obtain ⟨x, c, s, hy, C, hC, hc, hst, hout⟩ := h
      have hsh := shape_of_code hy C hc
      have hv := (acceptLang_iff N x (Nat.bits c) s).mp ⟨x, c, s, rfl, C, hC, hc, hst, hout⟩
      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv.1).1
    rw [hind]
    exact hhalt

/-! ## The initial code -/

variable (N) in
/-- The scan-state part of the initial-code test. -/
def InitScan (st : VSt N) : Prop :=
  VAcc N st ∧ st.2.1 = some (some N.tm.q₀, 0) ∧ st.2.2.2.2.2 = true

instance (st : VSt N) : Decidable (InitScan N st) := by unfold InitScan; infer_instance

/-- **The tail of the initial-code mode**: after the scan, test the scan state, the input
position (`= 1`) and, with work tapes, the head flag of tape `0` in the middle cell.

**Proof sketch.** A finite branch on the scan state; two zero tests around one decrement for
the position; for the middle cell, the address `a + 2(W s + hH + 2)` is computed by a copy, a
scale and an increment chain, and read through the bit oracle (`getD_w`). -/
theorem init_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (st : VAd N) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hT : R.T = 0) (hs : s ≤ 2 * y.length)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    AHalt (CA N .init) orc y (GuardLe (CA N .init) y (bnd N y)) (some (.vDone st), R.val, none)
      (decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true))) := by
  set B := bnd N y
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hyl : y.length = 2 * x.length + 2 * w.length + 4 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
  -- answering from a label whose instruction is `ret`
  have hret : ∀ (l : Lab N) (v : Fin 21 → ℕ) (b : Bool), (∀ r, v r ≤ B) →
      CA N .init l = .ret b → AHalt (CA N .init) orc y (GuardLe (CA N .init) y B) (some l, v, none) b :=
    fun l v b hv h => AHalt.ret h ⟨by simp [PreS, h], hv⟩
  have hv0 := hBd.val_le
  by_cases hscan : InitScan N st.1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hscan]]
    have r1 : Reach N .init y B (.vDone st) R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
        (by simp only [InitScan] at hscan; simp [astep, CA, goto, hscan])
    exact AReach.halt r1 (hret _ _ _ hv0 rfl)
  have r1 : Reach N .init y B (.vDone st) R.val .iz1 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
      (by simp only [InitScan] at hscan; simp [astep, CA, goto, hscan])
  by_cases hp0 : R.Pos = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp0]]
    have r2 : Reach N .init y B .iz1 R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA, hp0])
    exact AReach.halt (r1.trans r2) (hret _ _ _ hv0 rfl)
  have r2 : Reach N .init y B .iz1 R.val .iz2 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA, hp0])
  have hv1 : ({R with Pos := R.Pos - 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
  have r3 : Reach N .init y B .iz2 R.val .iz3 ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA])
  by_cases hp1 : R.Pos = 1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp1]]
    have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .rej
        ({R with Pos := R.Pos - 1} : Regs).val :=
      Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
        (by simp [astep, CA]; omega)
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le rfl)
  have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .icen
      ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA]; omega)
  set R1 : Regs := {R with Pos := R.Pos - 1}
  by_cases hk : N.k = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = true by simp [hscan, hp1, hk]]
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le (by simp [CA, hk]))
  -- the middle cell
  have hkpos : 1 ≤ N.k := Nat.one_le_iff_ne_zero.mpr hk
  have hWh : hH N + 3 ≤ W N := by simp [W]; omega
  have hidx : W N * s + (hH N + 2) < W N * (2 * s + 1) := by
    have : W N * (2 * s + 1) = W N * s + W N * s + W N := by ring
    have : 0 ≤ W N * s := Nat.zero_le _
    omega
  have hAB : R.A ≤ y.length := by rw [hA]; omega
  have r5 : Reach N .init y B .icen R1.val .clrUc R1.val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA, hk, goto])) (by simp [astep, CA, hk, goto])
  have r6 : Reach N .init y B .clrUc R1.val (.cp .Uc) ({R1 with U := 0} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA])
  have r7 : Reach N .init y B (.cp .Uc) ({R1 with U := 0} : Regs).val (.cp .Tsc)
      ({R1 with U := R.A} : Regs).val :=
    Reach.cast (cp_run y B .Uc _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc, R1])
  have r8 : Reach N .init y B (.cp .Tsc) ({R1 with U := R.A} : Regs).val (.sc .C)
      ({R1 with U := R.A, T := s} : Regs).val :=
    Reach.cast (cp_run y B .Tsc _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, R1, hT])) (by simp [cpDst, cpSrc, R1, hS])
  have hscl : R.A + 2 * W N * s + 2 * (hH N + 2) ≤ B := by
    have : 2 * W N * s + 2 * (hH N + 2) ≤ 2 * (W N * (2 * s + 1)) := by
      have : 2 * W N * s = 2 * (W N * s) := by ring
      omega
    omega
  have r9 : Reach N .init y B (.sc .C) ({R1 with U := R.A, T := s} : Regs).val (icL N .C 0)
      ({R1 with U := R.A + 2 * W N * s, T := 0} : Regs).val :=
    Reach.cast (sc_run y B .C _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor, R1]; omega)) (by simp [scDst, scSrc, scFactor, R1])
  have r10 : Reach N .init y B (icL N .C 0) ({R1 with U := R.A + 2 * W N * s, T := 0} : Regs).val
      .cenRead ({R1 with U := R.A + 2 * W N * s + 2 * (hH N + 2), T := 0} : Regs).val :=
    Reach.cast (ic_run y B .C _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [icReg, icCount, R1]; omega)) (by simp [icReg, icCount, R1])
  set R2 : Regs := {R1 with U := R.A + 2 * W N * s + 2 * (hH N + 2), T := 0}
  have hR2 : R2.Bd B := by simp only [R2, R1, Regs.Bd]; omega
  have hbit : y.getD (R.A + 2 * W N * s + 2 * (hH N + 2)) false =
      w.getD (W N * s + (hH N + 2)) false := by
    rw [hA, show 2 * x.length + 2 + 2 * W N * s + 2 * (hH N + 2) =
      2 * x.length + 2 + 2 * (W N * s + (hH N + 2)) by ring, hy, getD_w _ _ _ _ (by omega)]
  rw [List.getD_eq_getElem?_getD] at hbit
  rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
      (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) =
      w.getD (W N * s + (hH N + 2)) false by
    rw [List.getD_eq_getElem?_getD]; simp [hscan, hp1, hk]]
  rw [List.getD_eq_getElem?_getD]
  cases hb : (w[W N * s + (hH N + 2)]?).getD false
  · have r11 : Reach N .init y B .cenRead R2.val .rej R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)
  · have r11 : Reach N .init y B .cenRead R2.val .acc R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)

/-- **The initial code forms a logspace language** (`Complexity.Codec.initLang`).

**Proof sketch.** As `validLang_mem`, with the initial-code tail (`init_tail`) and the
initial-code check (`initLang_iff`). -/
theorem initLang_mem : initLang N ∈ LOGSPACE := by
  refine arm_decides_poly (CA N .init) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  rcases one_run (N := N) (mode := .init) (by decide) y with
    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, hPos, run⟩ | ⟨hfail, hhalt⟩
  · have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hsh.1, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hsh.2
    have hind : MultiTapeTM.indicator (initLang N : Set (List Bool)) y =
        decide (InitScan N st.1 ∧ R.Pos = 1 ∧
          (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) := by
      apply indicator_eq_of_iff
      rw [hsh.1, initLang_iff, InitChk, validChk_iff_pre, hst, InitScan, hPos]
      constructor
      · rintro ⟨⟨-, hv⟩, h2, h3, h4, h5⟩
        exact ⟨⟨hv, h2, h3⟩, h4, h5⟩
      · rintro ⟨⟨hv, h2, h3⟩, h4, h5⟩
        exact ⟨⟨hpre, hv⟩, h2, h3, h4, h5⟩
    rw [hind]
    exact AReach.halt run (init_tail y x w (Nat.bits s) hsh.1 R s st hR hA hS hT hs
      (by have := hpre.1; omega))
  · have hind : MultiTapeTM.indicator (initLang N : Set (List Bool)) y = false := by
      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
      · rfl
      obtain ⟨x, c, s, hy, hc⟩ := h
      have hsh := shape_of_code hy (N.tm.initCfg x) hc
      have hv := (initLang_iff N x (Nat.bits c) s).mp ⟨x, c, s, rfl, hc⟩
      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv.1).1
    rw [hind]
    exact hhalt

end Complexity.Codec
