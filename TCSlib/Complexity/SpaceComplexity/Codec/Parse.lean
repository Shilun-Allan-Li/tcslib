/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Run

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The codec machine parses its input

The first phase of the codec machine `Complexity.Codec.CA`: measure the input, parse the
pairs `⟨x, ⟨w, s⟩⟩` (or `⟨x, ⟨w, ⟨w', s⟩⟩⟩` for steps), check that the last field is a
canonical binary word of at most `|bits |y||` letters, and decode it. Either the input has
this shape and the machine reaches the layout phase with the field positions in its
registers, or it does not and the machine rejects.

Logspace machine infrastructure for the codec; not a result of [AB09].

## Main definitions

* `Complexity.Codec.bnd` — the register bound `(8 W + 8)(|y| + 1)`.
* `Complexity.Codec.Shape1`, `Complexity.Codec.Shape2` — the well-shaped inputs.

## Main results

* `Complexity.Codec.parse_run` — the parse phase, for one-code inputs.
* `Complexity.Codec.parse_run₂` — the parse phase, for step inputs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {mode : CMode}

variable (N) in
/-- The register bound of the codec machine on input `y`. -/
def bnd (y : List Bool) : ℕ := (8 * W N + 8) * (y.length + 1)

/-- The input length is below the register bound. -/
lemma length_le_bnd (y : List Bool) : y.length ≤ bnd N y := by
  unfold bnd
  calc y.length ≤ 1 * (y.length + 1) := by omega
    _ ≤ (8 * W N + 8) * (y.length + 1) := Nat.mul_le_mul_right _ (by omega)

/-! ## Positions in pairs -/

/-- Letter `i` of the first component of a pair sits at position `2i`. -/
lemma pe_getD_fst (u v : List Bool) (i : ℕ) (hi : i < u.length) :
    (pairEncode u v).getD (2 * i) false = u.getD i false := by
  rw [pairEncode_getD, if_pos (by omega)]
  congr 1; omega

/-- Letter `j` of the second component of a pair sits at position `2|u| + 2 + j`. -/
lemma pe_getD_snd (u v : List Bool) (j : ℕ) :
    (pairEncode u v).getD (2 * u.length + 2 + j) false = v.getD j false := by
  rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1; omega

/-- The second component of a pair is its suffix after `2|u| + 2` letters. -/
lemma pe_drop (u v : List Bool) : (pairEncode u v).drop (2 * u.length + 2) = v := by
  rw [pairEncode_eq_dbl, List.append_assoc, show 2 * u.length + 2 = (dbl u).length + 2 by simp,
    List.drop_append]
  simp

/-- A word whose last letter (default `true`) is `true` is canonical. -/
lemma canon_of_getLastD {w : List Bool} (h : w.getLastD true = true) : Canon w := by
  intro hw
  rwa [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hw, Option.getD_some] at h

/-- The last letter (default `true`) of a binary word is `true`. -/
lemma getLastD_bits (s : ℕ) : (Nat.bits s).getLastD true = true := by
  by_cases h : Nat.bits s = []
  · rw [h]; rfl
  · rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast h, Option.getD_some]
    exact canon_bits s h

/-- A word of at most `|bits L|` letters has value below `2L` (for `L ≥ 1`). -/
lemma bitsVal_le_of_width (w : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hw : w.length ≤ (Nat.bits L).length) (i : ℕ) : bitsVal (w.drop i) ≤ 2 * L := by
  have h1 : bitsVal (w.drop i) < 2 ^ (w.drop i).length := bitsVal_lt_two_pow _
  have h2 : (w.drop i).length ≤ (Nat.bits L).length := by simp; omega
  have h3 : 2 ^ (Nat.bits L).length ≤ 2 * L := by
    rw [Nat.size_eq_bits_len]
    have hpos : 1 ≤ Nat.size L := Nat.size_pos.mpr (by omega)
    have hlt : ¬ L < 2 ^ (Nat.size L - 1) := by
      rw [← Nat.size_le]; omega
    have e : 2 ^ Nat.size L = 2 * 2 ^ (Nat.size L - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
  omega

/-- A canonical word has last letter (default `true`) `true`. -/
lemma getLastD_of_canon {w : List Bool} (h : Canon w) : w.getLastD true = true := by
  by_cases hw : w = []
  · rw [hw]; rfl
  · rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hw, Option.getD_some]
    exact h hw

/-! ## Rejection -/

/-- A run into `rej` is a rejecting halt. -/
lemma halt_rej {y : List Bool} {B : ℕ} {l : Lab N} {v v' : Fin 21 → ℕ}
    (h : Reach N mode y B l v .rej v') (hv' : ∀ r, v' r ≤ B) :
    AHalt (CA N mode) orc y (GuardLe (CA N mode) y B) (some l, v, none) false :=
  AReach.halt h (AHalt.ret rfl ⟨by simp [PreS, CA], hv'⟩)

/-! ## The radius field -/

/-- **The radius phase**: from `.cp .Q1s` with the pointer at the last field `w`, the machine
reaches the layout phase with the value of `w` decoded into `rS` when `w` is canonical and
at most `|bits |y||` letters long, and rejects otherwise.

**Proof sketch.** Copy the pointer and the cap (`cp_run`), check the width
(`ct_run`: its verdict is exactly canonicity and the width bound), copy the end pointer, and
decode (`dc_run`, values bounded by `bitsVal_le_of_width`). -/
theorem sw_run (y : List Bool) (R : Regs) (p : ℕ) (hBd : R.Bd (bnd N y))
    (hL : R.L = y.length) (hP : R.P = p) (hp : p ≤ y.length) (hQ1 : R.Q1 = 0) (hCap : R.Cap = 0)
    (hQ2 : R.Q2 = 0) (hS : R.S = 0) (hT : R.T = 0) (hy : 1 ≤ y.length) :
    (Canon (y.drop p) ∧ (y.drop p).length ≤ (Nat.bits y.length).length ∧
      ∃ q1 cap, q1 ≤ bnd N y ∧ cap ≤ bnd N y ∧
        Reach N mode y (bnd N y) (.cp .Q1s) R.val (.cp .N1)
          ({R with Q1 := q1, Cap := cap, Q2 := p, S := bitsVal (y.drop p)} : Regs).val) ∨
    (¬ (Canon (y.drop p) ∧ (y.drop p).length ≤ (Nat.bits y.length).length) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y)) (some (.cp .Q1s), R.val, none)
        false) := by
  set B := bnd N y
  have hLB : y.length ≤ B := length_le_bnd y
  have h2L : 2 * y.length ≤ B := by
    have := Nat.mul_le_mul_right (y.length + 1) (show 2 ≤ 8 * W N + 8 by omega)
    simp only [B, bnd]; omega
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  -- copy the pointer and the cap
  have r1 : Reach N mode y B (.cp .Q1s) R.val (.cp .Cap) ({R with Q1 := p} : Regs).val :=
    Reach.cast (cp_run y B .Q1s R.val hBd.val_le (by simp [cpDst, cpSrc]; omega))
      (by simp [cpDst, cpSrc, hP])
  have r2 : Reach N mode y B (.cp .Cap) ({R with Q1 := p} : Regs).val (.ctTest true)
      ({R with Q1 := p, Cap := y.length} : Regs).val :=
    Reach.cast (cp_run y B .Cap _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc]; omega)) (by simp [cpDst, cpSrc, hL])
  have hlen : y.length = p + (y.drop p).length := by simp; omega
  obtain ⟨v', hv', hq1, hframe, r3⟩ := ct_run (N := N) (mode := mode) y B (y.drop p)
    ({R with Q1 := p, Cap := y.length} : Regs).val
    (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) (by simp [hL]; omega)
    (fun i _ => by simp)
  have hv'R : v' = ({R with Q1 := v' rQ1, Cap := v' rCap} : Regs).val := by
    funext r
    by_cases h1 : r = rQ1
    · subst h1; rfl
    · by_cases h2 : r = rCap
      · subst h2; rfl
      · rw [hframe r h1 h2]
        fin_cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2
  have hcap : ({R with Q1 := p, Cap := y.length} : Regs).val rCap = y.length := rfl
  rw [hcap] at r3
  have hc : (y.drop p).length ≤ (Nat.bits y.length).length ∧ (y.drop p).getLastD true = true ↔
      Canon (y.drop p) ∧ (y.drop p).length ≤ (Nat.bits y.length).length :=
    ⟨fun ⟨a, b⟩ => ⟨canon_of_getLastD b, a⟩, fun ⟨a, b⟩ => ⟨b, getLastD_of_canon a⟩⟩
  by_cases hok : (y.drop p).length ≤ (Nat.bits y.length).length ∧
      (y.drop p).getLastD true = true
  · left
    obtain ⟨hcan, hw⟩ := hc.mp hok
    rw [if_pos hok.1, if_pos hok.2] at r3
    refine ⟨hcan, hw, v' rQ1, v' rCap, hv' _, hv' _, ?_⟩
    have b1 := hv' rQ1
    have b2 := hv' rCap
    -- copy the end pointer and decode
    have r4 : Reach N mode y B (.cp .Q2) ({R with Q1 := v' rQ1, Cap := v' rCap} : Regs).val
        (.dcTest .S) ({R with Q1 := v' rQ1, Cap := v' rCap, Q2 := y.length} : Regs).val :=
      Reach.cast (cp_run y B .Q2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
        (by simp [cpDst, cpSrc]; omega)) (by simp [cpDst, cpSrc, hL])
    have r5 : Reach N mode y B (.dcTest .S)
        ({R with Q1 := v' rQ1, Cap := v' rCap, Q2 := y.length} : Regs).val (.cp .N1)
        ({R with Q1 := v' rQ1, Cap := v' rCap, Q2 := p, S := bitsVal (y.drop p)} : Regs).val :=
      Reach.cast (dc_run y B .S (y.drop p)
        (fun i _ => (bitsVal_le_of_width _ _ hy hw i).trans h2L)
        _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
        (by simp [dcPtr, dcBase, dcStride]; omega) (by simp [dcAcc, hS])
        (by simp [hT]) (fun i _ => by simp [dcBase, dcStride, hP]))
        (by simp [dcPtr, dcBase, dcAcc, hP])
    exact (r1.trans r2).trans ((Reach.cast r3 hv'R).trans (r4.trans r5))
  · right
    refine ⟨fun h => hok (hc.mpr h), ?_⟩
    rw [show (if (y.drop p).length ≤ (Nat.bits y.length).length then
        if (y.drop p).getLastD true then Lab.cp CpId.Q2 else Lab.rej else Lab.rej) = (Lab.rej : Lab N)
      by split_ifs with h1 h2 <;> first | rfl | exact absurd ⟨h1, h2⟩ hok] at r3
    exact halt_rej ((r1.trans r2).trans r3) hv'

/-! ## The whole parse -/

/-- The well-shaped one-code inputs `⟨x, ⟨w, bits s⟩⟩` whose radius field fits the width
check. -/
def Shape1 (y x w : List Bool) (s : ℕ) : Prop :=
  y = pairEncode x (pairEncode w (Nat.bits s)) ∧ (Nat.bits s).length ≤ (Nat.bits y.length).length

/-- The well-shaped step inputs `⟨x, ⟨w, ⟨w', bits s⟩⟩⟩` whose radius field fits the width
check. -/
def Shape2 (y x w w' : List Bool) (s : ℕ) : Prop :=
  y = pairEncode x (pairEncode w (pairEncode w' (Nat.bits s))) ∧
    (Nat.bits s).length ≤ (Nat.bits y.length).length

/-- The first parse step: measure the input and parse its first component.

**Proof sketch.** The length loop (`len_run`) sets `rL = |y|`; the aligned pair scan from
`0` (`pr_run`) rejects when `y` is not a pair and otherwise stops past `x` and the
separator; the pointer is copied into `rA` (`cp_run`). -/
theorem parse_x (y : List Bool) :
    (∃ x r, y = pairEncode x r ∧
      Reach N mode y (bnd N y) .lenScan ({} : Regs).val (.prScan 1)
        ({ L := y.length, P := 2 * x.length + 2, A := 2 * x.length + 2 } : Regs).val) ∨
    ((∀ x r, y ≠ pairEncode x r) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y)) (some .lenScan, ({} : Regs).val, none)
        false) := by
  set B := bnd N y
  have hLB : y.length ≤ B := length_le_bnd y
  have r0 : Reach N mode y B .lenScan ({} : Regs).val (.prScan 0)
      ({ L := y.length } : Regs).val :=
    Reach.cast (len_run y B hLB _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp)) (by simp)
  have h1 := pr_run (N := N) (mode := mode) y B 0 ({ L := y.length } : Regs).val
    (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) rfl (by simp)
  simp only [Regs.val_P, List.drop_zero] at h1
  cases hd : pairDecode y with
  | none =>
    rw [hd] at h1
    obtain ⟨t, ht, run⟩ := h1
    right
    refine ⟨fun x r h => (by rw [h, pairDecode_pairEncode] at hd; cases hd), ?_⟩
    refine halt_rej (r0.trans run) ?_
    rw [Regs.upd_P]
    apply Regs.Bd.val_le
    simp only [Regs.Bd]; omega
  | some xr =>
    obtain ⟨x, r⟩ := xr
    rw [hd] at h1
    have hy := eq_pairEncode_of_pairDecode y x r hd
    left
    refine ⟨x, r, hy, ?_⟩
    have hxl : 2 * x.length + 2 ≤ y.length := by rw [hy, length_pairEncode]; omega
    have r1 : Reach N mode y B (.prScan 0) ({ L := y.length } : Regs).val (.cp .A)
        ({ L := y.length, P := 2 * x.length + 2 } : Regs).val :=
      Reach.cast h1 (by simp)
    have r2 : Reach N mode y B (.cp .A) ({ L := y.length, P := 2 * x.length + 2 } : Regs).val
        (.prScan 1) ({ L := y.length, P := 2 * x.length + 2, A := 2 * x.length + 2 } : Regs).val :=
      Reach.cast (cp_run y B .A _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
        (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
    exact r0.trans (r1.trans r2)

/-- **The parse phase on one-code inputs**: a well-shaped input `⟨x, ⟨w, bits s⟩⟩` brings the
machine to the layout phase with `rL = |y|`, `rP = rQ2` at the radius field, `rA` at `w`,
`rS = s`; any other input is rejected.

**Proof sketch.** Measure and parse `x` (`parse_x`), parse `w` (`pr_run`), and treat the
radius field (`sw_run`). Each failure (no pair, no inner pair, a non-canonical or too long
radius field) rules out the shape, by injectivity of the pairing. -/
theorem parse_run (hm : mode ≠ .step) (y : List Bool) :
    (∃ (x w : List Bool) (s q1 cap : ℕ), Shape1 y x w s ∧ q1 ≤ bnd N y ∧ cap ≤ bnd N y ∧
      Reach N mode y (bnd N y) .lenScan ({} : Regs).val (.cp .N1)
        ({ L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
           Q1 := q1, Cap := cap, Q2 := 2 * x.length + 2 * w.length + 4, S := s } : Regs).val) ∨
    ((¬ ∃ x w s, Shape1 y x w s) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y)) (some .lenScan, ({} : Regs).val, none)
        false) := by
  set B := bnd N y
  have hLB : y.length ≤ B := length_le_bnd y
  rcases parse_x (N := N) (mode := mode) y with ⟨x, r, hy, r01⟩ | ⟨hno, hhalt⟩
  · have hdrop : y.drop (2 * x.length + 2) = r := by rw [hy, pe_drop]
    have hxl : 2 * x.length + 2 ≤ y.length := by rw [hy, length_pairEncode]; omega
    have h2 := pr_run (N := N) (mode := mode) y B 1
      ({ L := y.length, P := 2 * x.length + 2, A := 2 * x.length + 2 } : Regs).val
      (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) rfl (by simpa using hxl)
    simp only [Regs.val_P, hdrop] at h2
    cases hd : pairDecode r with
    | none =>
      rw [hd] at h2
      obtain ⟨t, ht, run⟩ := h2
      right
      refine ⟨?_, ?_⟩
      · rintro ⟨x', w', s', hs, -⟩
        rw [hy] at hs
        obtain ⟨-, hr⟩ := pairEncode_inj hs
        rw [hr, pairDecode_pairEncode] at hd; cases hd
      · refine halt_rej (r01.trans run) ?_
        rw [Regs.upd_P]
        apply Regs.Bd.val_le
        have hyl : y.length = 2 * x.length + 2 + r.length := by rw [hy, length_pairEncode]
        simp only [Regs.Bd]; omega
    | some ws =>
      obtain ⟨w, sw⟩ := ws
      rw [hd] at h2
      have hr := eq_pairEncode_of_pairDecode r w sw hd
      have hcont : prCont N mode 1 3 = .cp .Q1s := by simp [prCont, hm]
      rw [hcont] at h2
      have hlen : y.length = 2 * x.length + 2 * w.length + 4 + sw.length := by
        rw [hy, hr, length_pairEncode, length_pairEncode]; ring
      have hdrop2 : y.drop (2 * x.length + 2 * w.length + 4) = sw := by
        rw [show 2 * x.length + 2 * w.length + 4 = (2 * x.length + 2) + (2 * w.length + 2) by ring,
          ← List.drop_drop, hdrop, hr, pe_drop]
      have r2 : Reach N mode y B (.prScan 1)
          ({ L := y.length, P := 2 * x.length + 2, A := 2 * x.length + 2 } : Regs).val (.cp .Q1s)
          ({ L := y.length, P := 2 * x.length + 2 * w.length + 4,
             A := 2 * x.length + 2 } : Regs).val :=
        Reach.cast h2 (by simp; ring_nf)
      rcases sw_run (N := N) (mode := mode) y
        ({ L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2 } : Regs)
        (2 * x.length + 2 * w.length + 4) (by simp only [Regs.Bd]; omega) rfl rfl (by omega)
        rfl rfl rfl rfl rfl (by omega) with ⟨hcan, hw, q1, cap, hq1, hcap, run⟩ | ⟨hbad, hhalt⟩
      · left
        rw [hdrop2] at hcan hw run
        refine ⟨x, w, bitsVal sw, q1, cap, ⟨?_, ?_⟩, hq1, hcap, r01.trans (r2.trans run)⟩
        · rw [hy, hr, ← canon_eq_bits sw hcan]
        · rwa [← canon_eq_bits sw hcan]
      · right
        refine ⟨?_, AReach.halt (r01.trans r2) hhalt⟩
        rintro ⟨x', w', s', hs, hwid⟩
        rw [hdrop2] at hbad
        rw [hy] at hs
        obtain ⟨-, h1⟩ := pairEncode_inj hs
        rw [hr] at h1
        obtain ⟨-, h2⟩ := pairEncode_inj h1
        rw [h2] at hbad
        exact hbad ⟨canon_bits s', hwid⟩
  · right
    refine ⟨?_, hhalt⟩
    rintro ⟨x', w', s', hs, -⟩
    exact hno x' _ hs

/-- **The parse phase on step inputs**: a well-shaped input `⟨x, ⟨w, ⟨w', bits s⟩⟩⟩` brings
the step machine to the layout phase with `rA` at `w`, `rB` at `w'`, `rP = rQ2` at the
radius field and `rS = s`; any other input is rejected.

**Proof sketch.** As `parse_run`, with one more pair parse (`pr_run`) for `w'`. -/
theorem parse_run₂ (y : List Bool) :
    (∃ (x w w' : List Bool) (s q1 cap : ℕ), Shape2 y x w w' s ∧ q1 ≤ bnd N y ∧ cap ≤ bnd N y ∧
      Reach N .step y (bnd N y) .lenScan ({} : Regs).val (.cp .N1)
        ({ L := y.length, P := 2 * x.length + 2 * w.length + 2 * w'.length + 6,
           A := 2 * x.length + 2, B := 2 * x.length + 2 * w.length + 4, Q1 := q1, Cap := cap,
           Q2 := 2 * x.length + 2 * w.length + 2 * w'.length + 6, S := s } : Regs).val) ∨
    ((¬ ∃ x w w' s, Shape2 y x w w' s) ∧
      AHalt (CA N .step) orc y (GuardLe (CA N .step) y (bnd N y))
        (some .lenScan, ({} : Regs).val, none) false) := by
  set B := bnd N y
  have hLB : y.length ≤ B := length_le_bnd y
  rcases parse_x (N := N) (mode := .step) y with ⟨x, r, hy, r01⟩ | ⟨hno, hhalt⟩
  · have hdrop : y.drop (2 * x.length + 2) = r := by rw [hy, pe_drop]
    have hyl : y.length = 2 * x.length + 2 + r.length := by rw [hy, length_pairEncode]
    have h2 := pr_run (N := N) (mode := .step) y B 1
      ({ L := y.length, P := 2 * x.length + 2, A := 2 * x.length + 2 } : Regs).val
      (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) rfl (by simp; omega)
    simp only [Regs.val_P, hdrop] at h2
    cases hd : pairDecode r with
    | none =>
      rw [hd] at h2
      obtain ⟨t, ht, run⟩ := h2
      right
      refine ⟨?_, ?_⟩
      · rintro ⟨x', w', w'', s', hs, -⟩
        rw [hy] at hs
        obtain ⟨-, hr⟩ := pairEncode_inj hs
        rw [hr, pairDecode_pairEncode] at hd; cases hd
      · refine halt_rej (r01.trans run) ?_
        rw [Regs.upd_P]
        apply Regs.Bd.val_le
        simp only [Regs.Bd]; omega
    | some wr =>
      obtain ⟨w, r2⟩ := wr
      rw [hd] at h2
      have hr := eq_pairEncode_of_pairDecode r w r2 hd
      have hcont : prCont N .step 1 3 = .cp .B := by simp [prCont]
      rw [hcont] at h2
      have hyl2 : y.length = 2 * x.length + 2 * w.length + 4 + r2.length := by
        rw [hyl, hr, length_pairEncode]; ring
      have hdrop2 : y.drop (2 * x.length + 2 * w.length + 4) = r2 := by
        rw [show 2 * x.length + 2 * w.length + 4 = (2 * x.length + 2) + (2 * w.length + 2) by ring,
          ← List.drop_drop, hdrop, hr, pe_drop]
      have r2' : Reach N .step y B (.prScan 1)
          ({ L := y.length, P := 2 * x.length + 2, A := 2 * x.length + 2 } : Regs).val (.cp .B)
          ({ L := y.length, P := 2 * x.length + 2 * w.length + 4,
             A := 2 * x.length + 2 } : Regs).val :=
        Reach.cast h2 (by simp; ring_nf)
      have r3 : Reach N .step y B (.cp .B)
          ({ L := y.length, P := 2 * x.length + 2 * w.length + 4,
             A := 2 * x.length + 2 } : Regs).val (.prScan 2)
          ({ L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
             B := 2 * x.length + 2 * w.length + 4 } : Regs).val :=
        Reach.cast (cp_run y B .B _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
          (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
      have h3 := pr_run (N := N) (mode := .step) y B 2
        ({ L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
           B := 2 * x.length + 2 * w.length + 4 } : Regs).val
        (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) rfl (by simp; omega)
      simp only [Regs.val_P, hdrop2] at h3
      cases hd2 : pairDecode r2 with
      | none =>
        rw [hd2] at h3
        obtain ⟨t, ht, run⟩ := h3
        right
        refine ⟨?_, ?_⟩
        · rintro ⟨x', w', w'', s', hs, -⟩
          rw [hy] at hs
          obtain ⟨-, h1⟩ := pairEncode_inj hs
          rw [hr] at h1
          obtain ⟨-, h2⟩ := pairEncode_inj h1
          rw [h2, pairDecode_pairEncode] at hd2; cases hd2
        · refine halt_rej (r01.trans (r2'.trans (r3.trans run))) ?_
          rw [Regs.upd_P]
          apply Regs.Bd.val_le
          simp only [Regs.Bd]; omega
      | some ws =>
        obtain ⟨w', sw⟩ := ws
        rw [hd2] at h3
        have hr2 := eq_pairEncode_of_pairDecode r2 w' sw hd2
        have hcont2 : prCont N .step 2 3 = .cp .Q1s := rfl
        rw [hcont2] at h3
        have hyl3 : y.length = 2 * x.length + 2 * w.length + 2 * w'.length + 6 + sw.length := by
          rw [hyl2, hr2, length_pairEncode]; ring
        have hdrop3 : y.drop (2 * x.length + 2 * w.length + 2 * w'.length + 6) = sw := by
          rw [show 2 * x.length + 2 * w.length + 2 * w'.length + 6 =
              (2 * x.length + 2 * w.length + 4) + (2 * w'.length + 2) by ring,
            ← List.drop_drop, hdrop2, hr2, pe_drop]
        have r4 : Reach N .step y B (.prScan 2)
            ({ L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
               B := 2 * x.length + 2 * w.length + 4 } : Regs).val (.cp .Q1s)
            ({ L := y.length, P := 2 * x.length + 2 * w.length + 2 * w'.length + 6,
               A := 2 * x.length + 2, B := 2 * x.length + 2 * w.length + 4 } : Regs).val :=
          Reach.cast h3 (by simp; ring_nf)
        rcases sw_run (N := N) (mode := .step) y
          ({ L := y.length, P := 2 * x.length + 2 * w.length + 2 * w'.length + 6,
             A := 2 * x.length + 2, B := 2 * x.length + 2 * w.length + 4 } : Regs)
          (2 * x.length + 2 * w.length + 2 * w'.length + 6) (by simp only [Regs.Bd]; omega) rfl rfl
          (by omega) rfl rfl rfl rfl rfl (by omega)
          with ⟨hcan, hw, q1, cap, hq1, hcap, run⟩ | ⟨hbad, hhalt⟩
        · left
          rw [hdrop3] at hcan hw run
          refine ⟨x, w, w', bitsVal sw, q1, cap, ⟨?_, ?_⟩, hq1, hcap,
            r01.trans (r2'.trans (r3.trans (r4.trans run)))⟩
          · rw [hy, hr, hr2, ← canon_eq_bits sw hcan]
          · rwa [← canon_eq_bits sw hcan]
        · right
          refine ⟨?_, AReach.halt (r01.trans (r2'.trans (r3.trans r4))) hhalt⟩
          rintro ⟨x', w₁, w₂, s', hs, hwid⟩
          rw [hdrop3] at hbad
          rw [hy] at hs
          obtain ⟨-, h1⟩ := pairEncode_inj hs
          rw [hr] at h1
          obtain ⟨-, h2⟩ := pairEncode_inj h1
          rw [hr2] at h2
          obtain ⟨-, h3⟩ := pairEncode_inj h2
          rw [h3] at hbad
          exact hbad ⟨canon_bits s', hwid⟩
  · right
    refine ⟨?_, hhalt⟩
    rintro ⟨x', w', w'', s', hs, -⟩
    exact hno x' _ hs

end Complexity.Codec
