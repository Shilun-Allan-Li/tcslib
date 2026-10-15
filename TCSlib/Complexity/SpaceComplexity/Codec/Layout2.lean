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
# The step machine lays out the second code word and reads the input symbol

Two phases of the codec machine `Complexity.Codec.CA` in mode `step`: the layout of the second
code word `w'` (its chunk-region end `E₂`, its position-field end `F₂`, the length and
final-letter checks, the decoded input position), and the read of the input symbol under the
first word's input head into the register `rZ` (`0` for a blank, `1` for `0`, `2` for `1`),
followed by the pointer copies of the double sliding scan.

Logspace machine infrastructure for the codec; not a result of [AB09].

## Main definitions

* `Complexity.Codec.lay2R` — the register file after the second layout.
* `Complexity.Codec.zcode` — the register code of an input symbol.

## Main results

* `Complexity.Codec.layout2_run` — the layout of the second code word.
* `Complexity.Codec.insym_run` — the input-symbol read and the scan pointers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool}

/-- Letters of the second code word inside a step input. -/
lemma getD_w2 (x w w' rest : List Bool) (i : ℕ) (hi : i < w'.length) :
    (pairEncode x (pairEncode w (pairEncode w' rest))).getD
      (2 * x.length + 2 * w.length + 4 + 2 * i) false = w'.getD i false := by
  rw [show 2 * x.length + 2 * w.length + 4 + 2 * i = 2 * x.length + 2 + (2 * w.length + 2 + 2 * i)
    by ring, pe_getD_snd, pe_getD_snd, pe_getD_fst _ _ _ hi]

variable (N) in
/-- The register file after the layout of the second code word. -/
def lay2R (R : Regs) (b s wp pos : ℕ) : Regs :=
  { R with
    E2 := b + 4 * W N * s + 2 * W N, F2 := b + 4 * W N * s + 2 * W N + 2 * wp,
    U := b + 4 * W N * s + 2 * W N + 2 * wp + 4, Q1 := b + 4 * W N * s + 2 * W N,
    Pos2 := pos, T := 0 }

/-- **The layout of the second code word**: as `layout_run`, for `w'` starting at `rB`,
reusing `wP |x|` from `rWp`; the length check compares `F₂ + 4` with the start `rP` of the
radius field. The machine rejects exactly when `w'` has the wrong length or final letter, and
otherwise reaches the input-symbol read with the decoded position of `w'` in `rPos2`.

**Proof sketch.** The loop sequence of `layout_run` from the scale of the radius on, with
letters of `w'` at `b + 2i` (`getD_w2`). -/
theorem layout2_run (y x w w' rest : List Bool)
    (hy : y = pairEncode x (pairEncode w (pairEncode w' rest)))
    (R : Regs) (s : ℕ) (hBd : R.Bd (bnd N y)) (hB : R.B = 2 * x.length + 2 * w.length + 4)
    (hP : R.P = 2 * x.length + 2 * w.length + 2 * w'.length + 6) (hS : R.S = s)
    (hs : s ≤ 2 * y.length) (hWp : R.Wp = wP x.length) (hE2 : R.E2 = 0) (hF2 : R.F2 = 0)
    (hT : R.T = 0) (hPos2 : R.Pos2 = 0) :
    (w'.length = W N * (2 * s + 1) + wP x.length + 1 ∧
      w'.getD (W N * (2 * s + 1) + wP x.length) false = true ∧
      Reach N .step y (bnd N y) (.cp .E2) R.val .inZ
        (lay2R N R (2 * x.length + 2 * w.length + 4) s (wP x.length)
          (bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)))).val) ∨
    (¬ (w'.length = W N * (2 * s + 1) + wP x.length + 1 ∧
      w'.getD (W N * (2 * s + 1) + wP x.length) false = true) ∧
      AHalt (CA N .step) orc y (GuardLe (CA N .step) y (bnd N y)) (some (.cp .E2), R.val, none)
        false) := by
  set B := bnd N y
  set n := x.length
  set b := 2 * n + 2 * w.length + 4
  set e := b + 4 * W N * s + 2 * W N
  set f := e + 2 * wP n
  have hyl : y.length = b + 2 * w'.length + 2 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode, length_pairEncode]; simp only [b, n]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hwP := wP_le n
  have he2 : e = b + 2 * W N * (2 * s + 1) := by simp only [e]; ring
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have r5 : Reach N .step y B (.cp .E2) R.val (.cp .Ts2) ({R with E2 := b} : Regs).val :=
    Reach.cast (cp_run y B .E2 _ hBd.val_le (by simp [cpDst, cpSrc, hE2]))
      (by simp [cpDst, cpSrc, hB, b])
  have r6 : Reach N .step y B (.cp .Ts2) ({R with E2 := b} : Regs).val (.sc .E2)
      ({R with E2 := b, T := s} : Regs).val :=
    Reach.cast (cp_run y B .Ts2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hT])) (by simp [cpDst, cpSrc, hS])
  have r7 : Reach N .step y B (.sc .E2) ({R with E2 := b, T := s} : Regs).val (icL N .E2 0)
      ({R with E2 := b + 4 * W N * s, T := 0} : Regs).val :=
    Reach.cast (sc_run y B .E2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor]; omega)) (by simp [scDst, scSrc, scFactor])
  have r8 : Reach N .step y B (icL N .E2 0) ({R with E2 := b + 4 * W N * s, T := 0} : Regs).val
      (.cp .F2) ({R with E2 := e, T := 0} : Regs).val :=
    Reach.cast (ic_run y B .E2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [icReg, icCount]; omega)) (by simp [icReg, icCount, e])
  have r9 : Reach N .step y B (.cp .F2) ({R with E2 := e, T := 0} : Regs).val (.cp .Tw2)
      ({R with E2 := e, T := 0, F2 := e} : Regs).val :=
    Reach.cast (cp_run y B .F2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hF2])) (by simp [cpDst, cpSrc])
  have r10 : Reach N .step y B (.cp .Tw2) ({R with E2 := e, T := 0, F2 := e} : Regs).val (.sc .F2)
      ({R with E2 := e, T := wP n, F2 := e} : Regs).val :=
    Reach.cast (cp_run y B .Tw2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hWp])) (by simp [cpDst, cpSrc, hWp])
  have r11 : Reach N .step y B (.sc .F2) ({R with E2 := e, T := wP n, F2 := e} : Regs).val .clrU2
      ({R with E2 := e, T := 0, F2 := f} : Regs).val :=
    Reach.cast (sc_run y B .F2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor]; omega)) (by simp [scDst, scSrc, scFactor, f])
  have r12 : Reach N .step y B .clrU2 ({R with E2 := e, T := 0, F2 := f} : Regs).val (.cp .U2)
      ({R with E2 := e, T := 0, F2 := f, U := 0} : Regs).val :=
    Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [PreS, CA])) (by simp [astep, CA])
  have r13 : Reach N .step y B (.cp .U2) ({R with E2 := e, T := 0, F2 := f, U := 0} : Regs).val
      (icL N .U2 0) ({R with E2 := e, T := 0, F2 := f, U := f} : Regs).val :=
    Reach.cast (cp_run y B .U2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
  have r14 : Reach N .step y B (icL N .U2 0) ({R with E2 := e, T := 0, F2 := f, U := f} : Regs).val
      .lenChk2 ({R with E2 := e, T := 0, F2 := f, U := f + 4} : Regs).val :=
    Reach.cast (ic_run y B .U2 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [icReg, icCount]; omega)) (by simp [icReg, icCount])
  have r5_14 := r5.trans (r6.trans (r7.trans (r8.trans (r9.trans (r10.trans (r11.trans
    (r12.trans (r13.trans r14))))))))
  set R14 : Regs := {R with E2 := e, T := 0, F2 := f, U := f + 4}
  have hR14 : R14.Bd B := by simp only [R14, Regs.Bd]; omega
  by_cases hlen : w'.length = W N * (2 * s + 1) + wP n + 1
  · have heq : f + 4 = 2 * n + 2 * w.length + 2 * w'.length + 6 := by
      rw [hlen]; simp only [f, e, b]; ring
    have r15 : Reach N .step y B .lenChk2 R14.val .term2 R14.val :=
      Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]; decide))
        (by simp [astep, CA, R14, heq, hP])
    have hterm : y.getD f false = w'.getD (W N * (2 * s + 1) + wP n) false := by
      rw [show f = 2 * x.length + 2 * w.length + 4 + 2 * (W N * (2 * s + 1) + wP n) by
          simp only [f, e, b, n]; ring, hy, getD_w2 _ _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD] at hterm
    by_cases htm : w'.getD (W N * (2 * s + 1) + wP n) false = true
    · have htm' := htm
      rw [List.getD_eq_getElem?_getD] at htm'
      left
      refine ⟨hlen, htm, ?_⟩
      have r16 : Reach N .step y B .term2 R14.val .clrQ1b R14.val :=
        Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]))
          (by simp [astep, CA, vword_whole₁, orc_bit, R14, hterm, htm'])
      have r17 : Reach N .step y B .clrQ1b R14.val (.cp .Q1f2) ({R14 with Q1 := 0} : Regs).val :=
        Reach.single' (gd_of hR14.val_le (by simp [PreS, CA])) (by simp [astep, CA])
      have r18 : Reach N .step y B (.cp .Q1f2) ({R14 with Q1 := 0} : Regs).val (.dcTest .Pos2)
          ({R14 with Q1 := f} : Regs).val :=
        Reach.cast (cp_run y B .Q1f2 _ (by apply Regs.Bd.val_le; simp only [R14, Regs.Bd]; omega)
          (by simp [cpDst, cpSrc, R14])) (by simp [cpDst, cpSrc, R14])
      set pf := (w'.drop (W N * (2 * s + 1))).take (wP n)
      have hpf : pf.length = wP n := by simp only [pf, List.length_take, List.length_drop]; omega
      have hpow : 2 ^ wP n ≤ 2 * (n + 1) := two_pow_bits_le (n + 1) (by omega)
      have r19 : Reach N .step y B (.dcTest .Pos2) ({R14 with Q1 := f} : Regs).val .inZ
          ({R14 with Q1 := e, Pos2 := bitsVal pf} : Regs).val :=
        Reach.cast (dc_run y B .Pos2 pf
          (fun i _ => by
            have h1 := bitsVal_lt_two_pow (pf.drop i)
            have h2 : 2 ^ (pf.drop i).length ≤ 2 ^ wP n :=
              Nat.pow_le_pow_right (by norm_num) (by simp; omega)
            omega)
          _ (by apply Regs.Bd.val_le; simp only [R14, Regs.Bd]; omega)
          (by simp [dcPtr, dcBase, dcStride, R14, hpf, f])
          (by simp [dcAcc, R14, hPos2]) (by simp [R14])
          (fun i hi => by
            rw [hpf] at hi
            simp only [dcBase, dcStride, R14, Regs.val_E2]
            rw [hy,
              show e + 2 * i = 2 * x.length + 2 * w.length + 4 + 2 * (W N * (2 * s + 1) + i) by
                rw [he2]; simp only [b, n]; ring,
              getD_w2 _ _ _ _ _ (by omega)]
            simp only [pf, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi,
              List.getElem?_drop]))
          (by simp [dcPtr, dcBase, dcAcc, R14])
      refine (r5_14.trans (r15.trans (r16.trans (r17.trans (r18.trans r19))))).cast ?_
      simp only [lay2R, R14, e, f, b, pf, n]
    · have htm' : (w'[W N * (2 * s + 1) + wP n]?).getD false = false := by
        rw [← List.getD_eq_getElem?_getD]; simpa using htm
      right
      refine ⟨fun h => htm h.2, ?_⟩
      have r16 : Reach N .step y B .term2 R14.val .rej R14.val :=
        Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]))
          (by simp [astep, CA, vword_whole₁, orc_bit, R14, hterm, htm'])
      exact halt_rej (r5_14.trans (r15.trans r16)) hR14.val_le
  · right
    refine ⟨fun h => hlen h.1, ?_⟩
    have hne : ¬ f = 2 * n + 2 * w.length + 2 * w'.length + 2 := by
      intro h; apply hlen; simp only [f, e, b] at h
      have : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
      omega
    have r15 : Reach N .step y B .lenChk2 R14.val .rej R14.val :=
      Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]; decide))
        (by simp [astep, CA, R14, hP, hne])
    exact halt_rej (r5_14.trans r15) hR14.val_le

/-- The register code of an optional input symbol: `0` blank, `1` for `0`, `2` for `1`. -/
def zcode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- **The input-symbol read**: the machine stores the code of the input symbol under the
first word's input head (`inpOf`) in `rZ`, then copies the scan pointers `rQ3 := rA`,
`rQ4 := rB`.

**Proof sketch.** Zero and end tests on the position; otherwise copy the position, decrement,
double into `rU` (`sc_run`) — the address of input letter `pos - 1` in the doubled first
field — read it (`pe_getD_fst`) and count it into `rZ`; then two copies. -/
theorem insym_run (y x rest : List Bool) (hy : y = pairEncode x rest) (R : Regs)
    (hBd : R.Bd (bnd N y)) (hPos : R.Pos ≤ x.length + 1) (hN1 : R.N1 = x.length + 1)
    (hT : R.T = 0) (hZ : R.Z = 0) (hQ3 : R.Q3 = 0) (hQ4 : R.Q4 = 0) :
    ∃ u, u ≤ bnd N y ∧ Reach N .step y (bnd N y) .inZ R.val .clrQ1v
      ({R with Z := zcode (inpOf x R.Pos), U := u, Q3 := R.A, Q4 := R.B} : Regs).val := by
  set B := bnd N y
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hyl : y.length = 2 * x.length + 2 + rest.length := by rw [hy, length_pairEncode]
  have hLB : y.length ≤ B := length_le_bnd y
  -- the pointer copies
  have copies : ∀ R' : Regs, R'.Bd B → R'.Q3 = 0 → R'.Q4 = 0 →
      Reach N .step y B (.cp .Q3) R'.val .clrQ1v ({R' with Q3 := R'.A, Q4 := R'.B} : Regs).val := by
    intro R' hR' h3 h4
    have hR'0 := hR'
    simp only [Regs.Bd] at hR'0
    have c1 : Reach N .step y B (.cp .Q3) R'.val (.cp .Q4) ({R' with Q3 := R'.A} : Regs).val :=
      Reach.cast (cp_run y B .Q3 _ hR'.val_le (by simp [cpDst, cpSrc, h3])) (by simp [cpDst, cpSrc])
    have c2 : Reach N .step y B (.cp .Q4) ({R' with Q3 := R'.A} : Regs).val .clrQ1v
        ({R' with Q3 := R'.A, Q4 := R'.B} : Regs).val :=
      Reach.cast (cp_run y B .Q4 _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
        (by simp [cpDst, cpSrc, h4])) (by simp [cpDst, cpSrc])
    exact c1.trans c2
  by_cases h0 : R.Pos = 0
  · refine ⟨R.U, hB0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
    have r1 : Reach N .step y B .inZ R.val (.cp .Q3) R.val :=
      Reach.single' (gd_of hBd.val_le (by simp [PreS, CA])) (by simp [astep, CA, h0])
    have := copies R hBd hQ3 hQ4
    exact (r1.trans this).cast (by simp [inpOf, h0, zcode, hZ])
  have r1 : Reach N .step y B .inZ R.val .inN R.val :=
    Reach.single' (gd_of hBd.val_le (by simp [PreS, CA])) (by simp [astep, CA, h0])
  by_cases h1 : R.Pos = x.length + 1
  · refine ⟨R.U, hB0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
    have r2 : Reach N .step y B .inN R.val (.cp .Q3) R.val :=
      Reach.single' (gd_of hBd.val_le (by simp [PreS, CA]; decide)) (by simp [astep, CA, h1, hN1])
    have := copies R hBd hQ3 hQ4
    exact (r1.trans (r2.trans this)).cast (by simp [inpOf, h1, zcode, hZ])
  have r2 : Reach N .step y B .inN R.val (.cp .Tpos) R.val :=
    Reach.single' (gd_of hBd.val_le (by simp [PreS, CA]; decide))
      (by simp [astep, CA, hN1]; omega)
  have r3 : Reach N .step y B (.cp .Tpos) R.val .inDec ({R with T := R.Pos} : Regs).val :=
    Reach.cast (cp_run y B .Tpos _ hBd.val_le (by simp [cpDst, cpSrc, hT])) (by simp [cpDst, cpSrc])
  have r4 : Reach N .step y B .inDec ({R with T := R.Pos} : Regs).val .clrU3
      ({R with T := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [PreS, CA])) (by simp [astep, CA])
  have r5 : Reach N .step y B .clrU3 ({R with T := R.Pos - 1} : Regs).val (.sc .In)
      ({R with T := R.Pos - 1, U := 0} : Regs).val :=
    Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [PreS, CA])) (by simp [astep, CA])
  have r6 : Reach N .step y B (.sc .In) ({R with T := R.Pos - 1, U := 0} : Regs).val .inRead
      ({R with T := 0, U := 2 * (R.Pos - 1)} : Regs).val :=
    Reach.cast (sc_run y B .In _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor]; omega)) (by simp [scDst, scSrc, scFactor])
  set R6 : Regs := {R with T := 0, U := 2 * (R.Pos - 1)}
  have hR6 : R6.Bd B := by simp only [R6, Regs.Bd]; omega
  have hbit : y.getD (2 * (R.Pos - 1)) false = x.getD (R.Pos - 1) false := by
    rw [hy, pe_getD_fst _ _ _ (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hbit
  have hin : inpOf x R.Pos = some (x.getD (R.Pos - 1) false) := by
    simp [inpOf, h0, h1]
  refine ⟨2 * (R.Pos - 1), by omega, ?_⟩
  rw [hin, List.getD_eq_getElem?_getD]
  cases hb : (x[R.Pos - 1]?).getD false
  · have r7 : Reach N .step y B .inRead R6.val .inF R6.val :=
      Reach.single' (gd_of hR6.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R6, hbit, hb])
    have r8 : Reach N .step y B .inF R6.val (.cp .Q3) ({R6 with Z := 1} : Regs).val :=
      Reach.single' (gd_of hR6.val_le (by simp [PreS, CA])) (by simp [astep, CA, R6, hZ])
    have := copies ({R6 with Z := 1} : Regs) (by simp only [R6, Regs.Bd]; omega) (by simp [R6, hQ3])
      (by simp [R6, hQ4])
    exact (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans (r8.trans
      this)))))))).cast (by simp [R6, hT, zcode])
  · have r7 : Reach N .step y B .inRead R6.val .inT1 R6.val :=
      Reach.single' (gd_of hR6.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R6, hbit, hb])
    have r8 : Reach N .step y B .inT1 R6.val .inF ({R6 with Z := 1} : Regs).val :=
      Reach.single' (gd_of hR6.val_le (by simp [PreS, CA])) (by simp [astep, CA, R6, hZ])
    have r9 : Reach N .step y B .inF ({R6 with Z := 1} : Regs).val (.cp .Q3)
        ({R6 with Z := 2} : Regs).val :=
      Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [R6, Regs.Bd]; omega)
        (by simp [PreS, CA])) (by simp [astep, CA])
    have := copies ({R6 with Z := 2} : Regs) (by simp only [R6, Regs.Bd]; omega) (by simp [R6, hQ3])
      (by simp [R6, hQ4])
    exact (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans (r8.trans
      (r9.trans this))))))))).cast (by simp [R6, hT, zcode])

end Complexity.Codec
