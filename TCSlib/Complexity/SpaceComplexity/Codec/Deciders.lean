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

The codec machine `Complexity.Codec.CA` in the modes `valid`, `accept`, `init`, `edge` decides
the languages `Complexity.Codec.validLang N`, `acceptLang N`, `initLang N`, `edgeLang N`: it
parses (`parse_run`), lays out the code word (`layout_run`), compares the input position
(`le_phase`), scans the chunk region (`vscan_run`), and answers from the scan state — for
the initial code after testing the input position and the head flag of the middle cell, for an
edge code after testing, tape by tape, the head flags of the first and last cells.
`Complexity.LogProg.arm_decides_poly` turns this into membership in `L`.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
result of [AB09] by itself.

## Main definitions

* `Complexity.Codec.PreChk` — the checks done before the scan.
* `Complexity.Codec.InitScan` — the scan-state part of the initial-code test.

## Main results

* `Complexity.Codec.one_run` — the common run of the one-code modes.
* `Complexity.Codec.init_tail` — the tail of the initial-code mode.
* `Complexity.Codec.edge_round`, `Complexity.Codec.edge_loop`, `Complexity.Codec.edge_tail` —
  the tail of the edge-code mode.
* `Complexity.Codec.validLang_mem`, `Complexity.Codec.acceptLang_mem`,
  `Complexity.Codec.initLang_mem`, `Complexity.Codec.edgeLang_mem` — the four languages are in
  `L`.

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
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
        (some .lenScan, ({} : Regs).val, none)
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
      CA N .init l = .ret b →
        AHalt (CA N .init) orc y (GuardLe (CA N .init) y B) (some l, v, none) b :=
    fun l v b hv h => AHalt.ret h ⟨by simp [PreS, h], hv⟩
  have hv0 := hBd.val_le
  by_cases hscan : InitScan N st.1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hscan]]
    have r1 : Reach N .init y B (.vDone st) R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
        (by simp only [InitScan] at hscan
            simp [astep_jz (show CA N .init (.vDone st) = _ from rfl), hscan])
    exact AReach.halt r1 (hret _ _ _ hv0 rfl)
  have r1 : Reach N .init y B (.vDone st) R.val .iz1 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
      (by simp only [InitScan] at hscan; simp [astep_jz (show CA N .init (.vDone st) = _ from rfl),
        hscan])
  by_cases hp0 : R.Pos = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp0]]
    have r2 : Reach N .init y B .iz1 R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA]))
        (by simp [astep_jz (show CA N .init .iz1 = _ from rfl), hp0])
    exact AReach.halt (r1.trans r2) (hret _ _ _ hv0 rfl)
  have r2 : Reach N .init y B .iz1 R.val .iz2 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA]))
      (by simp [astep_jz (show CA N .init .iz1 = _ from rfl), hp0])
  have hv1 : ({R with Pos := R.Pos - 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
  have r3 : Reach N .init y B .iz2 R.val .iz3 ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA]))
      (by simp [astep_dec (show CA N .init .iz2 = _ from rfl)])
  by_cases hp1 : R.Pos = 1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp1]]
    have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .rej
        ({R with Pos := R.Pos - 1} : Regs).val :=
      Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
        (by simp [astep_jz (show CA N .init .iz3 = _ from rfl)]; omega)
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le rfl)
  have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .icen
      ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
      (by simp [astep_jz (show CA N .init .iz3 = _ from rfl)]; omega)
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
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA, hk, goto]))
      (by simp [astep_jz ((show CA N .init .icen = goto N .clrUc from if_neg hk).trans
        (goto_eq _))])
  have r6 : Reach N .init y B .clrUc R1.val (.cp .Uc) ({R1 with U := 0} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
      (by simp [astep_clr (show CA N .init .clrUc = _ from rfl)])
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
        (by simp [astep_call (show CA N .init .cenRead = _ from rfl), vword_whole₁,
          orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)
  · have r11 : Reach N .init y B .cenRead R2.val .acc R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep_call (show CA N .init .cenRead = _ from rfl), vword_whole₁,
          orc_bit, R2, hbit, hb])
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


/-! ## Edge codes

The edge-code mode reads, tape by tape, the head flags of the first and last cells of the chunk
region. Its run is proved from the table equations of `CA` at its labels (`CA_eRd1`, …), the
step equations of `astep` and the published loop runs, without unfolding `CA` or `astep`. -/

section Edge

variable (N) in
/-- The syntactic preconditions an instruction of the edge tail meets: distinct registers in an
equality test, distinct call arguments, and no input comparison. -/
private def EdgeOK : Ins 21 2 (Lab N) → Prop
  | .jeq r s _ _ => r ≠ s
  | .call _ _ args _ _ => args.Nodup
  | .jeqIn _ _ _ => False
  | .jeqFst _ _ _ => False
  | .jeqSnd _ _ _ => False
  | _ => True

variable {y : List Bool} {B : ℕ}

/-- The guard at a label of the edge tail, from its instruction's table equation. -/
private lemma edge_gd {l : Lab N} {v : Fin 21 → ℕ} (hv : ∀ r, v r ≤ B) {i : Ins 21 2 (Lab N)}
    (hl : CA N .edge l = i) (hi : EdgeOK N i) : GuardLe (CA N .edge) y B (some l, v, none) := by
  subst hl
  refine gd_of hv (preS_of_ins ?_ ?_ ?_ ?_ ?_)
  · intro r s l₁ l₀ h; rw [h] at hi; exact hi
  · intro j md args l₁ l₀ h; rw [h] at hi; exact hi
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim

/-- **One round of the edge loop**: from `eRd1` at tape `i`, with `U` at the head flag of tape
`i` in the first cell, `Q3 = q + 1` and `T = 0`, the machine answers `true` if tape `i`'s flag is
set in the first or the last cell, and otherwise reaches `eTest` with `Q3 = q` and the other
registers it reads unchanged.

**Proof sketch.** Read the flag at `U` (`orc_bit`, `getD_w`); on `1` answer `true`. Otherwise copy
`U` to `Q1`, add `4W · s` (copy `S` to `T`, then the scale loop) and read the flag of the last cell;
on `1` answer `true`. Otherwise count `Q3` down. -/
theorem edge_round (x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest)) (s : ℕ)
    (hw : W N * (2 * s + 1) ≤ w.length)
    (hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B) (hsB : s ≤ B)
    (i : ℕ) (hi : i < N.k) (q : ℕ) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hS : v rS = s) (hT : v rT = 0)
    (hU : v rU = 2 * x.length + 2 + 2 * (hH N + 3 * i + 2)) (hQ : v rQ3 = q + 1) :
    ((w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true) →
      AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y B) (some .eRd1, v, none) true) ∧
    (¬ (w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true) →
      ∃ v', Reach N .edge y B .eRd1 v .eTest v' ∧ (∀ r, v' r ≤ B) ∧
        v' rS = s ∧ v' rT = 0 ∧ v' rU = v rU ∧ v' rQ3 = q) := by
  have hW0 : hH N + 3 * i + 2 < W N := by rw [W_eq]; omega
  have hWs : W N * (2 * s + 1) = W N * (2 * s) + W N := by ring
  -- the flag of tape `i` in the first cell
  have hidx0 : hH N + 3 * i + 2 < w.length := by
    have : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hbit0 : y.getD (v rU) false = w.getD (hH N + 3 * i + 2) false := by
    rw [hU, hy]; exact getD_w x w rest _ hidx0
  have e1 : astep (CA N .edge) orc y (some .eRd1, v, none) =
      (some (if w.getD (hH N + 3 * i + 2) false = true then .acc else .eFar), v, none) := by
    rw [astep_call (CA_eRd1 .edge)]; simp only [vword_whole₁, orc_bit, hbit0]
  have hg1 : GuardLe (CA N .edge) y B (some .eRd1, v, none) :=
    edge_gd hv (CA_eRd1 .edge) (by simp [EdgeOK])
  have r1 : ¬ w.getD (hH N + 3 * i + 2) false = true → Reach N .edge y B .eRd1 v .eFar v :=
    fun h => Reach.single' hg1 (by rw [e1, if_neg h])
  -- the address of the flag in the last cell: `Q1 := U + 4W · s`
  set v1 := Function.update v rQ1 0 with hv1
  have hv1B : ∀ r, v1 r ≤ B := register_update_le _ rQ1 _ _ hv (Nat.zero_le _)
  have r2 : Reach N .edge y B .eFar v (.cp .Qe) v1 :=
    Reach.single' (edge_gd hv (CA_eFar .edge) trivial) (astep_clr (CA_eFar .edge))
  have h1U : v1 rU = v rU := by rw [hv1, Function.update_of_ne (by decide)]
  have h1Q : v1 rQ1 = 0 := by rw [hv1, Function.update_self]
  set v2 := Function.update v1 rQ1 (v rU) with hv2
  have hv2B : ∀ r, v2 r ≤ B := register_update_le _ rQ1 _ _ hv1B (hv rU)
  have r3 : Reach N .edge y B (.cp .Qe) v1 (.cp .Te) v2 := by
    have h := cp_run (N := N) (mode := .edge) y B .Qe v1 hv1B
      (by rw [cpDst_Qe, cpSrc_Qe, h1Q]; exact Nat.zero_le _)
    rwa [cpNext_Qe, cpDst_Qe, cpSrc_Qe, h1U] at h
  have h2T : v2 rT = 0 := by
    rw [hv2, Function.update_of_ne (by decide), hv1, Function.update_of_ne (by decide), hT]
  have h2S : v2 rS = s := by
    rw [hv2, Function.update_of_ne (by decide), hv1, Function.update_of_ne (by decide), hS]
  set v3 := Function.update v2 rT s with hv3
  have hv3B : ∀ r, v3 r ≤ B := register_update_le _ rT _ _ hv2B hsB
  have r4 : Reach N .edge y B (.cp .Te) v2 (.sc .Ee) v3 := by
    have h := cp_run (N := N) (mode := .edge) y B .Te v2 hv2B
      (by rw [cpDst_Te, cpSrc_Te, h2T]; exact Nat.zero_le _)
    rwa [cpNext_Te, cpDst_Te, cpSrc_Te, h2S] at h
  have h3T : v3 rT = s := by rw [hv3, Function.update_self]
  have h3Q : v3 rQ1 = v rU := by
    rw [hv3, Function.update_of_ne (by decide), hv2, Function.update_self]
  have hfar : v rU + 4 * W N * s ≤ B := by
    have : 4 * W N * s = 2 * (W N * (2 * s)) := by ring
    omega
  set v4 := Function.update (Function.update v3 rT 0) rQ1 (v rU + 4 * W N * s) with hv4
  have hv4B : ∀ r, v4 r ≤ B :=
    register_update_le _ rQ1 _ _ (register_update_le _ rT _ _ hv3B (Nat.zero_le _)) hfar
  have r5 : Reach N .edge y B (.sc .Ee) v3 .eRd2 v4 := by
    have h := sc_run (N := N) (mode := .edge) y B .Ee v3 hv3B
      (by rw [scDst_Ee, scSrc_Ee, scFactor_Ee, h3Q, h3T]; exact hfar)
    rwa [scNext_Ee, scDst_Ee, scSrc_Ee, scFactor_Ee, h3Q, h3T] at h
  -- the flag of tape `i` in the last cell
  have h4Q : v4 rQ1 = v rU + 4 * W N * s := by rw [hv4, Function.update_self]
  have hidx1 : W N * (2 * s) + (hH N + 3 * i + 2) < w.length := by omega
  have hbit1 : y.getD (v4 rQ1) false =
      w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false := by
    rw [h4Q, hU, hy, show 2 * x.length + 2 + 2 * (hH N + 3 * i + 2) + 4 * W N * s =
      2 * x.length + 2 + 2 * (W N * (2 * s) + (hH N + 3 * i + 2)) by ring]
    exact getD_w x w rest _ hidx1
  have e2 : astep (CA N .edge) orc y (some .eRd2, v4, none) =
      (some (if w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true then .acc else .eNext),
        v4, none) := by
    rw [astep_call (CA_eRd2 .edge)]; simp only [vword_whole₁, orc_bit, hbit1]
  have hg2 : GuardLe (CA N .edge) y B (some .eRd2, v4, none) :=
    edge_gd hv4B (CA_eRd2 .edge) (by simp [EdgeOK])
  -- count the tape down
  set v5 := Function.update v4 rQ3 (v4 rQ3 - 1) with hv5
  have hv5B : ∀ r, v5 r ≤ B :=
    register_update_le _ rQ3 _ _ hv4B (le_trans (Nat.sub_le _ _) (hv4B rQ3))
  have r6 : Reach N .edge y B .eNext v4 .eTest v5 :=
    Reach.single' (edge_gd hv4B (CA_eNext .edge) trivial) (astep_dec (CA_eNext .edge))
  constructor
  · intro hP
    by_cases hb0 : w.getD (hH N + 3 * i + 2) false = true
    · refine AHalt.step hg1 ?_
      rw [e1, if_pos hb0]
      exact AHalt.ret (CA_acc .edge) (edge_gd hv (CA_acc .edge) trivial)
    · have hb1 := hP.resolve_left hb0
      refine AReach.halt ((r1 hb0).trans (r2.trans (r3.trans (r4.trans r5)))) (AHalt.step hg2 ?_)
      rw [e2, if_pos hb1]
      exact AHalt.ret (CA_acc .edge) (edge_gd hv4B (CA_acc .edge) trivial)
  · intro hP
    rw [not_or] at hP
    refine ⟨v5, (r1 hP.1).trans (r2.trans (r3.trans (r4.trans (r5.trans
      ((Reach.single' hg2 (by rw [e2, if_neg hP.2])).trans r6))))), hv5B, ?_, ?_, ?_, ?_⟩
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hv3, Function.update_of_ne (by decide), h2S]
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_self]
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hv3, Function.update_of_ne (by decide), hv2,
        Function.update_of_ne (by decide), h1U]
    · have h4Q3 : v4 rQ3 = q + 1 := by
        rw [hv4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hv3,
          Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
          Function.update_of_ne (by decide), hQ]
      rw [hv5, Function.update_self, h4Q3, Nat.add_sub_cancel]

/-- **The edge loop**: from `eRd1` at tape `i`, with `U` at the head flag of tape `i` in the
first cell, `Q3 = k - i` and `T = 0`, the machine answers whether some tape `i' ≥ i` has its head
flag set in the first or the last cell of the chunk region.

**Proof sketch.** Induction on `k - i`, one tape per round (`edge_round`). After a round without
a set flag, `Q3` is tested: at `0` there is no further tape and the machine answers `false`;
otherwise `U` advances by `6` (two increment chains of `3`) to the next tape. -/
theorem edge_loop (x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest)) (s : ℕ)
    (hw : W N * (2 * s + 1) ≤ w.length)
    (hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B) (hsB : s ≤ B) :
    ∀ m (i : ℕ) (v : Fin 21 → ℕ), i + (m + 1) = N.k → (∀ r, v r ≤ B) →
      v rS = s → v rT = 0 → v rU = 2 * x.length + 2 + 2 * (hH N + 3 * i + 2) →
      v rQ3 = m + 1 →
      AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y B) (some .eRd1, v, none)
        (decide (∃ i' : Fin N.k, i ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro i v hik hv hS hT hU hQ
    obtain ⟨hyes, hno⟩ := edge_round x w rest hy s hw hB hsB i (by omega) 0 v hv hS hT hU hQ
    by_cases hP : w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true
    · rw [decide_eq_true ⟨⟨i, by omega⟩, le_rfl, hP⟩]; exact hyes hP
    · obtain ⟨v', r, hv'B, -, -, -, hQ'⟩ := hno hP
      rw [decide_eq_false (by
        rintro ⟨i', hle, hP'⟩
        have hi' : (i' : ℕ) = i := by have := i'.isLt; omega
        rw [hi'] at hP'
        exact hP hP')]
      refine AReach.halt r (AHalt.step (edge_gd hv'B (CA_eTest .edge) trivial) ?_)
      rw [astep_jz (CA_eTest .edge), if_pos hQ']
      exact AHalt.ret (CA_rej .edge) (edge_gd hv'B (CA_rej .edge) trivial)
  | succ m ih =>
    intro i v hik hv hS hT hU hQ
    obtain ⟨hyes, hno⟩ :=
      edge_round x w rest hy s hw hB hsB i (by omega) (m + 1) v hv hS hT hU hQ
    by_cases hP : w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true
    · rw [decide_eq_true ⟨⟨i, by omega⟩, le_rfl, hP⟩]; exact hyes hP
    · obtain ⟨v', r, hv'B, hS', hT', hU', hQ'⟩ := hno hP
      have r7 : Reach N .edge y B .eTest v' (icL N .S1 0) v' :=
        Reach.single' (edge_gd hv'B (CA_eTest .edge) trivial)
          (by rw [astep_jz (CA_eTest .edge), if_neg (by omega)])
      have hW1 : hH N + 3 * (i + 1) + 2 < W N := by rw [W_eq]; omega
      have hWs : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have hU6 : v' rU + 6 ≤ B := by omega
      set v6 := Function.update v' rU (v' rU + 3) with hv6
      have hv6B : ∀ r, v6 r ≤ B := register_update_le _ rU _ _ hv'B (by omega)
      have r8 : Reach N .edge y B (icL N .S1 0) v' (icL N .S2 0) v6 := by
        have h := ic_run (N := N) (mode := .edge) y B .S1 v' hv'B
          (by rw [icReg_S1, icCount_S1]; omega)
        rwa [icNext_S1, icReg_S1, icCount_S1, ← icL_zero] at h
      have h6U : v6 rU = v' rU + 3 := by rw [hv6, Function.update_self]
      set v7 := Function.update v6 rU (v6 rU + 3) with hv7
      have hv7B : ∀ r, v7 r ≤ B := register_update_le _ rU _ _ hv6B (by omega)
      have r9 : Reach N .edge y B (icL N .S2 0) v6 .eRd1 v7 := by
        have h := ic_run (N := N) (mode := .edge) y B .S2 v6 hv6B
          (by rw [icReg_S2, icCount_S2]; omega)
        rwa [icNext_S2, icReg_S2, icCount_S2] at h
      have h7 := ih (i + 1) v7 (by omega) hv7B
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hS'])
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hT'])
        (by rw [hv7, Function.update_self, h6U, hU', hU]; ring)
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hQ'])
      have hans : decide (∃ i' : Fin N.k, i ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) =
          decide (∃ i' : Fin N.k, i + 1 ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) := by
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨i', hle, hP'⟩
          refine ⟨i', ?_, hP'⟩
          rcases Nat.lt_or_ge i (i' : ℕ) with h | h
          · omega
          · have hi' : (i' : ℕ) = i := by omega
            rw [hi'] at hP'
            exact absurd hP' hP
        · rintro ⟨i', hle, hP'⟩
          exact ⟨i', by omega, hP'⟩
      rw [hans]
      exact AReach.halt (r.trans (r7.trans (r8.trans r9))) h7

end Edge


/-- **The tail of the edge-code mode**: after the scan, test the scan state and, tape by tape,
the head flags of the first and last cells.

**Proof sketch.** A finite branch on the scan state (`CA_vDone_edge`). Without work tapes the
machine answers `false`. Otherwise it sets `U` to the address `a + 2(hH + 2)` of tape `0`'s flag
in the first cell (a clear, a copy and an increment chain) and the tape counter `Q3` to `k`,
and runs the edge loop (`edge_loop`). -/
theorem edge_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (st : VAd N) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hT : R.T = 0) (hs : s ≤ 2 * y.length)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y (bnd N y)) (some (.vDone st), R.val, none)
      (decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true)) := by
  set B := bnd N y
  have hv0 := hBd.val_le
  have hyl : y.length = 2 * x.length + 2 * w.length + 4 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B := by
    have : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
    omega
  have hsB : s ≤ B := by omega
  have e0 : astep (CA N .edge) orc y (some (.vDone st), R.val, none) =
      (some (if VAcc N st.1 then .eStart else .rej), R.val, none) := by
    rw [astep_jz ((CA_vDone_edge st).trans (goto_eq _)), ite_self]
  have hg0 : GuardLe (CA N .edge) y B (some (.vDone st), R.val, none) :=
    edge_gd hv0 ((CA_vDone_edge st).trans (goto_eq _)) trivial
  by_cases hacc : VAcc N st.1
  swap
  · rw [decide_eq_false (fun h => hacc h.1)]
    refine AHalt.step hg0 ?_
    rw [e0, if_neg hacc]
    exact AHalt.ret (CA_rej .edge) (edge_gd hv0 (CA_rej .edge) trivial)
  have r0 : Reach N .edge y B (.vDone st) R.val .eStart R.val :=
    Reach.single' hg0 (by rw [e0, if_pos hacc])
  by_cases hk : N.k = 0
  · rw [decide_eq_false (fun ⟨_, i, _⟩ => absurd i.isLt (by omega))]
    exact AReach.halt r0 (AHalt.ret (CA_eStart_of_zero .edge hk)
      (edge_gd hv0 (CA_eStart_of_zero .edge hk) trivial))
  -- the address of tape `0`'s flag in the first cell, and the tape counter
  set v1 := Function.update R.val rU 0 with hv1
  have hv1B : ∀ r, v1 r ≤ B := register_update_le _ rU _ _ hv0 (Nat.zero_le _)
  have r1 : Reach N .edge y B .eStart R.val (.cp .Ue) v1 :=
    Reach.single' (edge_gd hv0 (CA_eStart_of_pos .edge hk) trivial)
      (astep_clr (CA_eStart_of_pos .edge hk))
  have h1A : v1 rA = R.A := by rw [hv1, Function.update_of_ne (by decide), Regs.val_A]
  set v2 := Function.update v1 rU R.A with hv2
  have hv2B : ∀ r, v2 r ≤ B := register_update_le _ rU _ _ hv1B (by rw [hA]; omega)
  have r2 : Reach N .edge y B (.cp .Ue) v1 (icL N .Eh 0) v2 := by
    have h := cp_run (N := N) (mode := .edge) y B .Ue v1 hv1B
      (by rw [cpDst_Ue, cpSrc_Ue, hv1, Function.update_self]; exact Nat.zero_le _)
    rwa [cpNext_Ue, cpDst_Ue, cpSrc_Ue, h1A, ← icL_zero] at h
  have h2U : v2 rU = R.A := by rw [hv2, Function.update_self]
  have hW0 : hH N + 2 < W N := by rw [W_eq]; omega
  have hWs : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  set v3 := Function.update v2 rU (R.A + 2 * (hH N + 2)) with hv3
  have hv3B : ∀ r, v3 r ≤ B := register_update_le _ rU _ _ hv2B (by omega)
  have r3 : Reach N .edge y B (icL N .Eh 0) v2 .eK v3 := by
    have h := ic_run (N := N) (mode := .edge) y B .Eh v2 hv2B
      (by rw [icReg_Eh, icCount_Eh, h2U]; omega)
    rwa [icNext_Eh, icReg_Eh, icCount_Eh, h2U] at h
  set v4 := Function.update v3 rQ3 0 with hv4
  have hv4B : ∀ r, v4 r ≤ B := register_update_le _ rQ3 _ _ hv3B (Nat.zero_le _)
  have r4 : Reach N .edge y B .eK v3 (icL N .Ke 0) v4 :=
    Reach.single' (edge_gd hv3B (CA_eK .edge) trivial) (astep_clr (CA_eK .edge))
  have hkB : N.k - 1 + 1 ≤ B := by
    have : N.k ≤ W N := by rw [W_eq]; omega
    omega
  set v5 := Function.update v4 rQ3 (N.k - 1 + 1) with hv5
  have hv5B : ∀ r, v5 r ≤ B := register_update_le _ rQ3 _ _ hv4B hkB
  have r5 : Reach N .edge y B (icL N .Ke 0) v4 .eRd1 v5 := by
    have h := ic_run (N := N) (mode := .edge) y B .Ke v4 hv4B
      (by rw [icReg_Ke, icCount_Ke, hv4, Function.update_self]; omega)
    rwa [icNext_Ke, icReg_Ke, icCount_Ke, hv4, Function.update_self, Nat.zero_add] at h
  have hloop := edge_loop (y := y) (B := B) x w rest hy s hw hB hsB (N.k - 1) 0 v5 (by omega)
    hv5B
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
      Function.update_of_ne (by decide), Regs.val_S, hS])
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
      Function.update_of_ne (by decide), Regs.val_T, hT])
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_self, hA])
    (by rw [hv5, Function.update_self])
  rw [show decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
      w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true) =
      decide (∃ i' : Fin N.k, 0 ≤ (i' : ℕ) ∧ (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) from
    decide_eq_decide.mpr ⟨fun ⟨_, i, h⟩ => ⟨i, Nat.zero_le _, h⟩,
      fun ⟨i, _, h⟩ => ⟨hacc, i, h⟩⟩]
  exact AReach.halt (r0.trans (r1.trans (r2.trans (r3.trans (r4.trans r5))))) hloop

/-- **Edge codes form a logspace language** (`Complexity.Codec.edgeLang`).

**Proof sketch.** As `validLang_mem`, with the edge-code tail (`edge_tail`) and the edge-code
check (`edgeLang_iff`). -/
theorem edgeLang_mem : edgeLang N ∈ LOGSPACE := by
  refine arm_decides_poly (CA N .edge) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  rw [← orc_eq]
  rcases one_run (N := N) (mode := .edge) (by decide) y with
    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, -, run⟩ | ⟨hfail, hhalt⟩
  · have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hsh.eq, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hsh.width
    have hind : MultiTapeTM.indicator (edgeLang N : Set (List Bool)) y =
        decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
          w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true) := by
      apply indicator_eq_of_iff
      rw [hsh.eq, edgeLang_iff, edgeChk_def, validChk_iff_pre, hst]
      exact ⟨fun ⟨⟨_, hv⟩, h⟩ => ⟨hv, h⟩, fun ⟨hv, h⟩ => ⟨⟨hpre, hv⟩, h⟩⟩
    rw [hind]
    exact AReach.halt run (edge_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs
      (by have := hpre.1; omega))
  · have hind : MultiTapeTM.indicator (edgeLang N : Set (List Bool)) y = false := by
      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
      · rfl
      obtain ⟨x, c, s, hy, C, hC, hc, -⟩ := (mem_edgeLang_iff N y).mp h
      have hsh := shape_of_code hy C hc
      have hv := (edgeLang_iff N x (Nat.bits c) s).mp (hy ▸ h)
      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp ((edgeChk_def N x s _).mp hv).1).1
    rw [hind]
    exact hhalt

end Complexity.Codec
