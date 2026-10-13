/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Parse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The codec machine lays out a code word and scans it

The second phase of the codec machine `Complexity.Codec.CA`: from the field positions of
the parse and the radius `s`, compute `|x| + 1`, the position-field width `wP |x|`, the end
`E` of the chunk region and the end `F` of the position field of the code word `w`; check the
length of `w` and its final letter; decode the input position. The machine rejects exactly
when the length or the final letter is wrong.

Logspace machine infrastructure for the codec; not a result of [AB09].

## Main definitions

* `Complexity.Codec.layR` — the register file after the layout phase.

## Main results

* `Complexity.Codec.two_pow_bits_le`, `Complexity.Codec.wP_le` — width arithmetic.
* `Complexity.Codec.layout_run` — the layout phase of the first code word.
* `Complexity.Codec.le_phase` — the position comparison.
* `Complexity.Codec.vscan_run` — the validity scan.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {mode : CMode}

/-- `2 ^ |bits L| ≤ 2L` for `L ≥ 1`. -/
lemma two_pow_bits_le (L : ℕ) (hL : 1 ≤ L) : 2 ^ (Nat.bits L).length ≤ 2 * L := by
  rw [Nat.size_eq_bits_len]
  have hpos : 1 ≤ Nat.size L := Nat.size_pos.mpr (by omega)
  have hlt : ¬ L < 2 ^ (Nat.size L - 1) := by
    rw [← Nat.size_le]; omega
  have e : 2 ^ Nat.size L = 2 * 2 ^ (Nat.size L - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- The position-field width is at most `n + 1`. -/
lemma wP_le (n : ℕ) : wP n ≤ n + 1 := by
  have h1 := length_bits_le_log (n + 1)
  have h2 := Nat.log_lt_self 2 (show n + 1 ≠ 0 by omega)
  simp only [wP]
  omega

/-- Letters of the first code word inside the input. -/
lemma getD_w (x w rest : List Bool) (i : ℕ) (hi : i < w.length) :
    (pairEncode x (pairEncode w rest)).getD (2 * x.length + 2 + 2 * i) false = w.getD i false := by
  rw [pe_getD_snd, pe_getD_fst _ _ _ hi]

/-- The register bound dominates the layout arithmetic. -/
lemma bnd_ge (y : List Bool) (s : ℕ) (hs : s ≤ 2 * y.length) :
    y.length + 2 * W N * (2 * s + 1) + 2 * (y.length + 1) + 4 ≤ bnd N y := by
  unfold bnd
  have h1 : 2 * W N * (2 * s + 1) ≤ 2 * W N * (4 * y.length + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e1 : 2 * W N * (4 * y.length + 1) = 8 * (W N * y.length) + 2 * W N := by ring
  have e2 : (8 * W N + 8) * (y.length + 1) = 8 * (W N * y.length) + 8 * W N + 8 * y.length + 8 := by
    ring
  omega

/-- A register file's valuation at an `if` between two registers. -/
lemma Regs.val_ite (R : Regs) (c : Prop) [Decidable c] (r r' : Fin 21) :
    R.val (if c then r else r') = if c then R.val r else R.val r' := by
  split <;> rfl

variable (N) in
/-- The register file after the layout phase. -/
def layR (R : Regs) (n s pos : ℕ) : Regs :=
  { R with
    N1 := n + 1, Wp := wP n, E := 2 * n + 2 + 4 * W N * s + 2 * W N,
    F := 2 * n + 2 + 4 * W N * s + 2 * W N + 2 * wP n,
    U := 2 * n + 2 + 4 * W N * s + 2 * W N + 2 * wP n + 4,
    Q1 := 2 * n + 2 + 4 * W N * s + 2 * W N, Pos := pos }

/-- **The layout phase**: on an input `⟨x, ⟨w, …⟩⟩` with the radius `s` in `rS`, the machine
computes `|x| + 1`, the field width `wP |x|`, the chunk-region end `E`, the position-field
end `F`; it rejects unless `w` has the code length (compared through `F + 4` with the start
of the next field) and ends with `1`; otherwise it decodes the input position and reaches
the position comparison.

**Proof sketch.** A straight sequence of the loop families: copy and halve (`cp_run`, one
`half`), count the width (`hc_run`), scale and add (`sc_run`, `ic_run`) to get
`E = a + 2W(2s + 1)` and `F = E + 2 wP`, compare `F + 4` with the next field's start (the
code length), read the final letter, and decode the position field at stride two
(`dc_run`). Letters of `w` sit at `a + 2i` (`getD_w`). -/
theorem layout_run (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (hBd : R.Bd (bnd N y)) (hL : R.L = y.length) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hs : s ≤ 2 * y.length) (hN1 : R.N1 = 0) (hWp : R.Wp = 0) (hE : R.E = 0)
    (hF : R.F = 0) (hT : R.T = 0) (hU : R.U = 0) (hPos : R.Pos = 0)
    (hcmp : (if mode = .step then R.B else R.P) = 2 * x.length + 2 * w.length + 4) :
    (w.length = W N * (2 * s + 1) + wP x.length + 1 ∧
      w.getD (W N * (2 * s + 1) + wP x.length) false = true ∧
      Reach N mode y (bnd N y) (.cp .N1) R.val .leT1
        (layR N R x.length s (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))).val) ∨
    (¬ (w.length = W N * (2 * s + 1) + wP x.length + 1 ∧
      w.getD (W N * (2 * s + 1) + wP x.length) false = true) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y)) (some (.cp .N1), R.val, none) false) := by
  set B := bnd N y
  set n := x.length
  set a := 2 * n + 2
  set e := a + 4 * W N * s + 2 * W N
  set f := e + 2 * wP n
  have hyl : y.length = a + 2 * w.length + 2 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hwP := wP_le n
  have he2 : e = a + 2 * W N * (2 * s + 1) := by simp only [e]; ring
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  -- the arithmetic
  have r1 : Reach N mode y B (.cp .N1) R.val .halveN ({R with N1 := a} : Regs).val :=
    Reach.cast (cp_run y B .N1 R.val hBd.val_le (by simp [cpDst, cpSrc]; omega))
      (by simp [cpDst, cpSrc, hA, a])
  have r2 : Reach N mode y B .halveN ({R with N1 := a} : Regs).val (.cp .Tn)
      ({R with N1 := n + 1} : Regs).val :=
    Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) (by simp [PreS, CA]))
      (by simp [astep, CA, a])
  have r3 : Reach N mode y B (.cp .Tn) ({R with N1 := n + 1} : Regs).val .hcTest
      ({R with N1 := n + 1, T := n + 1} : Regs).val :=
    Reach.cast (cp_run y B .Tn _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hT])) (by simp [cpDst, cpSrc])
  have r4 : Reach N mode y B .hcTest ({R with N1 := n + 1, T := n + 1} : Regs).val (.cp .E)
      ({R with N1 := n + 1, Wp := wP n} : Regs).val :=
    Reach.cast (hc_run y B _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [hWp]; simp only [wP] at hwP; omega)) (by simp [hWp, hT, wP])
  have r5 : Reach N mode y B (.cp .E) ({R with N1 := n + 1, Wp := wP n} : Regs).val (.cp .Ts)
      ({R with N1 := n + 1, Wp := wP n, E := a} : Regs).val :=
    Reach.cast (cp_run y B .E _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hE])) (by simp [cpDst, cpSrc, hA, a])
  have r6 : Reach N mode y B (.cp .Ts) ({R with N1 := n + 1, Wp := wP n, E := a} : Regs).val
      (.sc .E) ({R with N1 := n + 1, Wp := wP n, E := a, T := s} : Regs).val :=
    Reach.cast (cp_run y B .Ts _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hT])) (by simp [cpDst, cpSrc, hS])
  have r7 : Reach N mode y B (.sc .E) ({R with N1 := n + 1, Wp := wP n, E := a, T := s} : Regs).val
      (icL N .E 0) ({R with N1 := n + 1, Wp := wP n, E := a + 4 * W N * s, T := 0} : Regs).val :=
    Reach.cast (sc_run y B .E _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor]; omega)) (by simp [scDst, scSrc, scFactor])
  have r8 : Reach N mode y B (icL N .E 0)
      ({R with N1 := n + 1, Wp := wP n, E := a + 4 * W N * s, T := 0} : Regs).val (.cp .F)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0} : Regs).val :=
    Reach.cast (ic_run y B .E _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [icReg, icCount]; omega)) (by simp [icReg, icCount, e])
  have r9 : Reach N mode y B (.cp .F)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0} : Regs).val (.cp .Tw)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := e} : Regs).val :=
    Reach.cast (cp_run y B .F _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, hF])) (by simp [cpDst, cpSrc])
  have r10 : Reach N mode y B (.cp .Tw)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := e} : Regs).val (.sc .F)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := wP n, F := e} : Regs).val :=
    Reach.cast (cp_run y B .Tw _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
  have r11 : Reach N mode y B (.sc .F)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := wP n, F := e} : Regs).val .clrU
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f} : Regs).val :=
    Reach.cast (sc_run y B .F _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor]; omega)) (by simp [scDst, scSrc, scFactor, f])
  have r12 : Reach N mode y B .clrU
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f} : Regs).val (.cp .U)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f, U := 0} : Regs).val :=
    Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [PreS, CA])) (by simp [astep, CA])
  have r13 : Reach N mode y B (.cp .U)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f, U := 0} : Regs).val (icL N .U 0)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f, U := f} : Regs).val :=
    Reach.cast (cp_run y B .U _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
  have r14 : Reach N mode y B (icL N .U 0)
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f, U := f} : Regs).val .lenChk
      ({R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f, U := f + 4} : Regs).val :=
    Reach.cast (ic_run y B .U _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [icReg, icCount]; omega)) (by simp [icReg, icCount])
  have r1_14 := r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans (r8.trans
    (r9.trans (r10.trans (r11.trans (r12.trans (r13.trans r14))))))))))))
  set R14 : Regs := {R with N1 := n + 1, Wp := wP n, E := e, T := 0, F := f, U := f + 4}
  have hR14 : R14.Bd B := by simp only [R14, Regs.Bd]; omega
  have hcmp' : R14.val (if mode = .step then rB else rP) = 2 * n + 2 * w.length + 4 := by
    rw [Regs.val_ite]; simpa [R14] using hcmp
  have hneq : (if mode = .step then rB else rP) ≠ rU := by split <;> decide
  by_cases hlen : w.length = W N * (2 * s + 1) + wP n + 1
  · have heq : f + 4 = 2 * n + 2 * w.length + 4 := by
      rw [hlen]; simp only [f, e, a]; ring
    have r15 : Reach N mode y B .lenChk R14.val .term R14.val :=
      Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]; exact fun h => hneq h.symm))
        (by simp only [astep, CA]; rw [hcmp']; simp [R14, heq])
    have hterm : y.getD f false = w.getD (W N * (2 * s + 1) + wP n) false := by
      rw [show f = 2 * x.length + 2 + 2 * (W N * (2 * s + 1) + wP n) by
          simp only [f, e, a, n]; ring, hy, getD_w _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD] at hterm
    by_cases htm : w.getD (W N * (2 * s + 1) + wP n) false = true
    · have htm' := htm
      rw [List.getD_eq_getElem?_getD] at htm'
      left
      refine ⟨hlen, htm, ?_⟩
      have r16 : Reach N mode y B .term R14.val .clrQ1 R14.val :=
        Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]))
          (by simp [astep, CA, vword_whole₁, orc_bit, R14, hterm, htm'])
      have r17 : Reach N mode y B .clrQ1 R14.val (.cp .Q1f) ({R14 with Q1 := 0} : Regs).val :=
        Reach.single' (gd_of hR14.val_le (by simp [PreS, CA])) (by simp [astep, CA])
      have r18 : Reach N mode y B (.cp .Q1f) ({R14 with Q1 := 0} : Regs).val (.dcTest .Pos)
          ({R14 with Q1 := f} : Regs).val :=
        Reach.cast (cp_run y B .Q1f _ (by apply Regs.Bd.val_le; simp only [R14, Regs.Bd]; omega)
          (by simp [cpDst, cpSrc, R14])) (by simp [cpDst, cpSrc, R14])
      set pf := (w.drop (W N * (2 * s + 1))).take (wP n)
      have hpf : pf.length = wP n := by simp only [pf, List.length_take, List.length_drop]; omega
      have hpow : 2 ^ wP n ≤ 2 * (n + 1) := two_pow_bits_le (n + 1) (by omega)
      have r19 : Reach N mode y B (.dcTest .Pos) ({R14 with Q1 := f} : Regs).val .leT1
          ({R14 with Q1 := e, Pos := bitsVal pf} : Regs).val :=
        Reach.cast (dc_run y B .Pos pf
          (fun i _ => by
            have h1 := bitsVal_lt_two_pow (pf.drop i)
            have h2 : 2 ^ (pf.drop i).length ≤ 2 ^ wP n :=
              Nat.pow_le_pow_right (by norm_num) (by simp; omega)
            omega)
          _ (by apply Regs.Bd.val_le; simp only [R14, Regs.Bd]; omega)
          (by simp [dcPtr, dcBase, dcStride, R14, hpf, f])
          (by simp [dcAcc, R14, hPos]) (by simp [R14])
          (fun i hi => by
            rw [hpf] at hi
            simp only [dcBase, dcStride, R14, Regs.val_E]
            rw [hy, show e + 2 * i = 2 * x.length + 2 + 2 * (W N * (2 * s + 1) + i) by
                rw [he2]; simp only [a, n]; ring,
              getD_w _ _ _ _ (by omega)]
            simp only [pf, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi,
              List.getElem?_drop]))
          (by simp [dcPtr, dcBase, dcAcc, R14])
      refine (r1_14.trans (r15.trans (r16.trans (r17.trans (r18.trans r19))))).cast ?_
      simp only [layR, R14, e, f, a, pf, n, hT]
    · have htm' : (w[W N * (2 * s + 1) + wP n]?).getD false = false := by
        rw [← List.getD_eq_getElem?_getD]; simpa using htm
      right
      refine ⟨fun h => htm h.2, ?_⟩
      have r16 : Reach N mode y B .term R14.val .rej R14.val :=
        Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]))
          (by simp [astep, CA, vword_whole₁, orc_bit, R14, hterm, htm'])
      exact halt_rej (r1_14.trans (r15.trans r16)) hR14.val_le
  · right
    refine ⟨fun h => hlen h.1, ?_⟩
    have hne : f + 4 ≠ 2 * n + 2 * w.length + 4 := by
      intro h; apply hlen; simp only [f, e, a] at h
      have : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
      omega
    have r15 : Reach N mode y B .lenChk R14.val .rej R14.val :=
      Reach.single' (gd_of hR14.val_le (by simp [PreS, CA]; exact fun h => hneq h.symm))
        (by
          have hne' : ¬ f = 2 * n + 2 * w.length := by omega
          simp only [astep, CA]; rw [hcmp']; simp [R14, hne'])
    exact halt_rej (r1_14.trans r15) hR14.val_le

/-! ## The position comparison and the validity scan -/


/-- **The position comparison**: with `rT = 0`, a position at most `rN1` continues (to the
second code word for steps, to the scan otherwise) with `rT` cleared again; a larger
position is rejected.

**Proof sketch.** `le_run`, then one `clr`. -/
theorem le_phase (y : List Bool) (R : Regs) (hBd : R.Bd (bnd N y)) (hT : R.T = 0) :
    (R.Pos ≤ R.N1 → Reach N mode y (bnd N y) .leT1 R.val
      (if mode = .step then .cp .E2 else .clrQ1v) R.val) ∧
    (¬ R.Pos ≤ R.N1 →
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y)) (some .leT1, R.val, none) false) := by
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have h := le_run (N := N) (mode := mode) y (bnd N y) R.val hBd.val_le (by simpa using hT)
  simp only [Regs.val_Pos, Regs.val_N1, Regs.upd_T] at h
  constructor
  · intro hle
    rw [if_pos hle] at h
    refine h.trans ?_
    refine Reach.single' (gd_of ?_ (by simp [PreS, CA])) ?_
    · apply Regs.Bd.val_le; simp only [Regs.Bd]; omega
    · simp [astep, CA]
      have : ({R with T := 0} : Regs) = R := by cases R; simp_all
      rw [this]
  · intro hle
    rw [if_neg hle] at h
    exact halt_rej h (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)

/-- **The validity scan**: from `.clrQ1v`, with `rA` at the start of the code word `w` and
`rE` at the end of its chunk region (`W (2s + 1)` letters, inside `w`), the machine clears
and sets both scan pointers to `rA` and runs the validity scan over the region, ending in
`vDone` of the scan state whose first component is `vScan` of the region.

**Proof sketch.** Two clears and two copies set the pointers; the scan engine (`v_run`) reads
the region at stride two (`getD_w`), and its final state is by definition the adaptor fold
whose first component is `vScan`. -/
theorem vscan_run (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hE : R.E = 2 * x.length + 2 + 4 * W N * s + 2 * W N)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    ∃ st : VAd N, st.1 = vScan N (w.take (W N * (2 * s + 1))) ∧
      Reach N mode y (bnd N y) .clrQ1v R.val (.vDone st) ({R with Q1 := R.E, Q2 := R.E} : Regs).val := by
  set B := bnd N y
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hE' : R.E = R.A + 2 * (W N * (2 * s + 1)) := by rw [hE, hA]; ring
  have r1 : Reach N mode y B .clrQ1v R.val .clrQ2v ({R with Q1 := 0} : Regs).val :=
    Reach.single' (gd_of hBd.val_le (by simp [PreS, CA])) (by simp [astep, CA])
  have r2 : Reach N mode y B .clrQ2v ({R with Q1 := 0} : Regs).val (.cp .Q1a)
      ({R with Q1 := 0, Q2 := 0} : Regs).val :=
    Reach.single' (gd_of (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [PreS, CA])) (by simp [astep, CA])
  have r3 : Reach N mode y B (.cp .Q1a) ({R with Q1 := 0, Q2 := 0} : Regs).val (.cp .Q2a)
      ({R with Q1 := R.A, Q2 := 0} : Regs).val :=
    Reach.cast (cp_run y B .Q1a _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
  have r4 : Reach N mode y B (.cp .Q2a) ({R with Q1 := R.A, Q2 := 0} : Regs).val (.vTest (vAd0 N))
      ({R with Q1 := R.A, Q2 := R.A} : Regs).val :=
    Reach.cast (cp_run y B .Q2a _ (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc])
  set u := w.take (W N * (2 * s + 1))
  have hu : u.length = W N * (2 * s + 1) := by simp only [u, List.length_take]; omega
  have ho : ∀ i < u.length, y.getD (R.A + 2 * i) false = u.getD i false := by
    intro i hi
    rw [hu] at hi
    rw [hA, hy, getD_w _ _ _ _ (by omega)]
    simp only [u, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]
  have r5 := v_run (N := N) (mode := mode) y B u u rfl (vAd0 N)
    ({R with Q1 := R.A, Q2 := R.A} : Regs).val
    (by apply Regs.Bd.val_le; simp only [Regs.Bd]; omega) (by simp [hu, hE'])
    (by simp [hu]; omega) (by simpa using ho) (by simpa using ho)
  refine ⟨_, rfl, (r1.trans (r2.trans (r3.trans r4))).trans (Reach.cast r5 ?_)⟩
  simp [hu, hE']

end Complexity.Codec
