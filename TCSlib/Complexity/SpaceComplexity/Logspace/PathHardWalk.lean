/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The layout walk of the `PATH` query machine

The last phase of `Complexity.PathHard.A`: with the decoded index `i`, the vertex exponent
`E`, `2n = 2 ^ (E + 1)` and `2n² = 2 ^ (2E + 1)` in registers, the machine walks the layout
of the reduction's output — the unary block `1²ⁿ`, the separator `01`, the doubled adjacency
word, the tail `01 01 1` — and answers the bit at `i` (or, in length mode, whether `i` is
inside). Inside the adjacency word the offset `k` gives the vertex pair
`(k/2 / 2^E, k/2 % 2^E)` by halving and shifting, and the edge bit is asked from the code
deciders (`dispatch_halt`).

Infrastructure for [AB09, §4.3, Theorem 4.18]; not itself a result of the book.

## Main definitions

* `Complexity.PathHard.wAns` — the answer of the walk.

## Main results

* `Complexity.PathHard.dispatch_halt` — the edge bit of a vertex pair.
* `Complexity.PathHard.tail_halt` — the tail of the layout.
* `Complexity.PathHard.walk_halt` — the whole walk.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg

variable {a b f : ℕ} {mode : Bool} {B : ℕ} (N : FinNDTM Bool) (x β : List Bool)

/-! ## The edge relation at small vertices -/

/-- No edge leaves `0` towards `0` or `1`. -/
lemma not_edge_zero (s v : ℕ) (hv : v < 2) : ¬ Edge N x s 0 v := by
  rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega

/-- Edges from `0` go to initial codes. -/
lemma edge_zero_iff (s v : ℕ) : Edge N x s 0 (v + 2) ↔
    pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.initLang N := by
  constructor
  · rintro (⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · simpa using h
    · omega
    · omega
  · intro h; exact Or.inl ⟨rfl, by omega, by simpa using h⟩

/-- No edge leaves `1`. -/
lemma not_edge_one (s v : ℕ) : ¬ Edge N x s 1 v := by
  rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega

/-- No edge enters `0`. -/
lemma not_edge_to_zero (s u : ℕ) : ¬ Edge N x s u 0 := by
  rintro (⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩) <;> omega

/-- Edges into `1` come from accepting codes. -/
lemma edge_to_one_iff (s u : ℕ) : Edge N x s (u + 2) 1 ↔
    pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.acceptLang N := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩)
    · omega
    · simpa using h
    · omega
  · intro h; exact Or.inr (Or.inl ⟨by omega, rfl, by simpa using h⟩)

/-- Edges between code vertices are step pairs. -/
lemma edge_codes_iff (s u v : ℕ) : Edge N x s (u + 2) (v + 2) ↔ Codec.StepRel N x s u v := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩)
    · omega
    · omega
    · simpa using h
  · intro h; exact Or.inr (Or.inr ⟨by omega, by omega, by simpa using h⟩)

/-! ## The dispatch -/

/-- A classical decision of a false proposition is `false`. -/
lemma cdec_false {P : Prop} (h : ¬ P) : @decide P (Classical.dec P) = false :=
  @decide_eq_false _ (Classical.dec P) h

/-- Answering a decision: the machine at `if p then ans true else ans false` answers `p`. -/
lemma ans_dec {y : List Bool} {o : Fin 5 → List Bool → Bool} {st : St} (hbd : st.Bd B)
    {q p : Bool} (h : q = p) :
    AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B)
      (some (if q = true then .ans true else .ans false), st.toV, none) p := by
  subst h; cases q <;> exact ans_halt hbd _

/-- **The dispatch**: from `dU` with source `u` and target `v` in registers `u`, `i`, the
machine answers the edge bit `Edge x s u v`.

**Proof sketch.** Peel `u ∈ {0, 1, ≥ 2}` and `v ∈ {0, 1, ≥ 2}` by zero tests and decrements;
the impossible combinations answer `0`, and the others ask the initial-code (`u = 0`), the
accepting-code (`v = 1`) or the step decider with the codes `v - 2`, `u - 2`. -/
theorem dispatch_halt (st : St) (hbd : st.Bd B) :
    AHalt (A a b f false) (orc N) (pairEncode x β) (GuardLe (A a b f false) (pairEncode x β) B)
      (some .dU, st.toV, none) (@decide (Edge N x st.s st.u st.i) (Classical.dec _)) := by
  obtain ⟨y, p, xx, t, c, s, e, n, m, k, q, i, d, u, z⟩ := st
  simp only at hbd ⊢
  rcases u with _ | _ | u
  · refine stepH_of hbd ?_; stp
    rcases i with _ | _ | i
    · refine stepH_of hbd ?_; stp
      rw [cdec_false (not_edge_zero N x _ 0 (by omega))]
      exact ans_halt hbd _
    · refine stepH_of hbd ?_; stp
      refine stepH_of hbd ?_; stp
      refine stepH_of (by sbd) ?_; stp
      rw [cdec_false (not_edge_zero N x _ 1 (by omega))]
      exact ans_halt (by sbd) _
    · refine stepH_of hbd ?_; stp
      refine stepH_of hbd ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_
      simp only [astep, A, vword_whole₂]
      stp
      exact ans_dec (by sbd)
        ((orc_init N x β i s).trans (decide_eq_decide.mpr (edge_zero_iff N x s i)).symm)
  · refine stepH_of hbd ?_; stp
    refine stepH_of hbd ?_; stp
    refine stepH_of (by sbd) ?_; stp
    rw [cdec_false (not_edge_one N x _ _)]
    exact ans_halt (by sbd) _
  · refine stepH_of hbd ?_; stp
    refine stepH_of hbd ?_; stp
    refine stepH_of (by sbd) ?_; stp
    refine stepH_of (by sbd) ?_; stp
    rcases i with _ | _ | i
    · refine stepH_of (by sbd) ?_; stp
      rw [cdec_false (not_edge_to_zero N x _ _)]
      exact ans_halt (by sbd) _
    · refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_
      simp only [astep, A, vword_whole₂]
      stp
      exact ans_dec (by sbd)
        ((orc_acc N x β u s).trans (decide_eq_decide.mpr (edge_to_one_iff N x s u)).symm)
    · refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_; stp
      refine stepH_of (by sbd) ?_
      simp only [astep, A, vword_whole₃]
      stp
      exact ans_dec (by sbd)
        ((orc_step N x β u i s).trans (decide_eq_decide.mpr (edge_codes_iff N x s u i)).symm)

/-! ## The tail -/

/-- The answer at offset `r` into the tail `0 1 0 1 1` (every tail position counts in length
mode; beyond the tail, `0`). -/
def tailVal (mode : Bool) (r : ℕ) : Bool := if h : r < 5 then tailAns mode ⟨r, h⟩ else false

/-- **The tail**: from `tl 0` with offset `r` in register `i`, the machine answers
`tailVal mode r`.

**Proof sketch.** Five zero tests, separated by decrements. -/
theorem tail_halt {o : Fin 5 → List Bool → Bool} {y : List Bool} (st : St) (hbd : st.Bd B) :
    AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.tl 0), st.toV, none)
      (tailVal mode st.i) := by
  obtain ⟨y', p, xx, t, c, s, e, n, m, k, q, i, d, u, z⟩ := st
  simp only at hbd ⊢
  have go : ∀ (j : Fin 5) (r : ℕ), r ≤ i →
      AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B)
        (some (.tl j), (St.mk y' p xx t c s e n m k q r d u z).toV, none)
        (tailVal mode (j.val + r)) := by
    intro j r hr
    induction r generalizing j with
    | zero =>
      refine stepH_of (by sbd) ?_; stp
      simp only [tailVal, dif_pos j.isLt]
      exact ans_halt (by sbd) _
    | succ r ih =>
      refine stepH_of (by sbd) ?_; stp
      by_cases hj : j.val < 4
      · simp only [dif_pos hj]
        refine stepH_of (by sbd) ?_; stp
        have := ih ⟨j.val + 1, by omega⟩ (by omega)
        simp only at this
        rw [show j.val + (r + 1) = j.val + 1 + r by omega]
        exact this
      · simp only [dif_neg hj]
        have : tailVal mode (j.val + (r + 1)) = false := by
          simp only [tailVal]; rw [dif_neg (by omega)]
        rw [this]
        exact ans_halt (by sbd) _
  simpa using go 0 i le_rfl

/-! ## The matrix -/

/-- **A matrix letter**: from `mh` with the offset `k` into the doubled adjacency word in
register `i`, the machine answers (in bit mode) the edge bit of `(k/2 / 2^E, k/2 % 2^E)`,
and (in length mode) `1`.

**Proof sketch.** Halve `k`; copy it into `u` and divide by `2 ^ E` (`hv_run`); copy `u` into
`t`, shift it by `E` (`sh_run`) and subtract it from `k/2` (`sb_run`), leaving
`k/2 % 2^E`; then `dispatch_halt`. -/
theorem matrix_halt (st : St) (hbd : st.Bd B) (hu : st.u = 0) (ht : st.t = 0)
    (hc : st.c = 0) (hz : st.z = 0) :
    AHalt (A a b f mode) (orc N) (pairEncode x β)
      (GuardLe (A a b f mode) (pairEncode x β) B) (some .mh, st.toV, none)
      (if mode then true else @decide (Edge N x st.s (st.i / 2 / 2 ^ st.e)
        (st.i / 2 % 2 ^ st.e)) (Classical.dec _)) := by
  cases mode with
  | true =>
    exact AHalt.ret rfl (gb_of hbd _)
  | false =>
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨y', p, xx, t, c, s, e, n, m, k, q, i, d, u, z⟩ := st
    simp only at hbd hu ht hc hz ⊢
    subst hu ht hc hz
    set j := i / 2 with hj
    have hji : j ≤ i := Nat.div_le_self _ _
    have hq : j / 2 ^ e * 2 ^ e ≤ j := Nat.div_mul_le_self _ _
    refine stepH_of hbd ?_; stp
    -- `u := j`
    have h1 := cp_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) .UI (St.mk y' p xx 0 0 s e n m k q j d 0 0) (by sbd)
      (by simp [cpDst, cpSrc])
    regs [cpDst, cpSrc, cpNext] at h1
    refine h1.halt ?_
    -- `c := e`
    have h2 := cp_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) .CU (St.mk y' p xx 0 0 s e n m k q j d j 0) (by sbd)
      (by simp [cpDst, cpSrc])
    regs [cpDst, cpSrc, cpNext] at h2
    refine h2.halt ?_
    -- `u := j / 2 ^ e`
    have h3 := hv_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) (St.mk y' p xx 0 e s e n m k q j d j 0) (by sbd)
    refine h3.halt ?_
    simp only
    -- `t := u`
    have h4 := cp_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) .TU (St.mk y' p xx 0 0 s e n m k q j d (j / 2 ^ e) 0)
      (by have := Nat.div_le_self j (2 ^ e); sbd) (by simp [cpDst, cpSrc])
    regs [cpDst, cpSrc, cpNext] at h4
    refine h4.halt ?_
    -- `c := e`
    have h5 := cp_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) .CT
      (St.mk y' p xx (j / 2 ^ e) 0 s e n m k q j d (j / 2 ^ e) 0)
      (by have := Nat.div_le_self j (2 ^ e); sbd) (by simp [cpDst, cpSrc])
    regs [cpDst, cpSrc, cpNext] at h5
    refine h5.halt ?_
    -- `t := u · 2 ^ e`
    have h6 := sh_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) .T
      (St.mk y' p xx (j / 2 ^ e) e s e n m k q j d (j / 2 ^ e) 0)
      (by have := Nat.div_le_self j (2 ^ e); sbd) rfl (by simp [shReg]; sbd)
    regs [shReg, shExit] at h6
    refine h6.halt ?_
    -- `i := j - t`
    have h7 := sb_run (a := a) (b := b) (f := f) (mode := false) (o := orc N)
      (y := pairEncode x β) (B := B) .T
      (St.mk y' p xx (j / 2 ^ e * 2 ^ e) 0 s e n m k q j d (j / 2 ^ e) 0)
      (by have := Nat.div_le_self j (2 ^ e); sbd)
    regs [sbReg, sbExit] at h7
    refine h7.halt ?_
    have e1 : j - j / 2 ^ e * 2 ^ e = j % 2 ^ e := by
      rw [Nat.mod_def, mul_comm]
    have h8 := dispatch_halt (a := a) (b := b) (f := f) (B := B) N x β
      (St.mk y' p xx 0 0 s e n m k q (j - j / 2 ^ e * 2 ^ e) d (j / 2 ^ e) 0)
      (by have := Nat.div_le_self j (2 ^ e); sbd)
    rw [← e1]
    exact h8

/-! ## The walk -/

/-- **The answer of the walk** at index `i`, with `n = 2 ^ E` and radius `s`: in length mode,
whether `i < 2n² + 2n + 7`; in bit mode, the bit at `i` of the layout `1²ⁿ 01 M' 01 01 1`,
`M'` the doubled adjacency word of `Edge` on `n` vertices. -/
noncomputable def wAns (mode : Bool) (s E i : ℕ) : Bool :=
  if mode then decide (i < 2 * (2 ^ E) ^ 2 + 2 * 2 ^ E + 7)
  else if i < 2 * 2 ^ E then true
  else if i = 2 * 2 ^ E then false
  else if i = 2 * 2 ^ E + 1 then true
  else if i - (2 * 2 ^ E + 2) < 2 * (2 ^ E) ^ 2 then
    @decide (Edge N x s ((i - (2 * 2 ^ E + 2)) / 2 / 2 ^ E) ((i - (2 * 2 ^ E + 2)) / 2 % 2 ^ E))
      (Classical.dec _)
  else [false, true, false, true, true].getD (i - (2 * 2 ^ E + 2) - 2 * (2 ^ E) ^ 2) false

/-- **The walk**: from the first comparison, with `n = 2 ^ e`, `2n` and `2n²` in registers
`n`, `m`, the index in `i` and the scratch registers clear, the machine answers
`wAns mode s e i`.

**Proof sketch.** Compare `2n ≤ i` (`le_run`): below, the bit is in the unary block. Else
subtract `2n` (`sb_run`); offsets `0` and `1` are the separator; else subtract two more and
compare `2n² ≤ k` for the remaining offset `k`: below, a matrix letter (`matrix_halt`); else
subtract `2n²` and read the tail (`tail_halt`). -/
theorem walk_halt (st : St) (hbd : st.Bd B) (hd : st.d = 0) (hu : st.u = 0) (ht : st.t = 0)
    (hc : st.c = 0) (hz : st.z = 0) (hn : st.n = 2 * 2 ^ st.e)
    (hm : st.m = 2 * (2 ^ st.e) ^ 2) :
    AHalt (A a b f mode) (orc N) (pairEncode x β)
      (GuardLe (A a b f mode) (pairEncode x β) B) (some (.le .N 0), st.toV, none)
      (wAns N x mode st.s st.e st.i) := by
  obtain ⟨y', p, xx, t, c, s, e, n, m, k, q, i, d, u, z⟩ := st
  simp only at hbd hd hu ht hc hz hn hm ⊢
  subst hd hu ht hc hz hn hm
  have h1 := le_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N)
    (y := pairEncode x β) (B := B) .N (St.mk y' p xx 0 0 s e (2 * 2 ^ e) (2 * (2 ^ e) ^ 2) k q
      i 0 0 0) hbd rfl
  regs [leReg, leYes, leNo] at h1
  by_cases h2 : 2 * 2 ^ e ≤ i
  · rw [if_pos h2] at h1
    refine h1.halt ?_
    refine stepH_of (by sbd) ?_; stp
    have h3 := sb_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N)
      (y := pairEncode x β) (B := B) .N (St.mk y' p xx 0 0 s e (2 * 2 ^ e) (2 * (2 ^ e) ^ 2) k q
        i 0 0 0) hbd
    regs [sbReg, sbExit] at h3
    refine h3.halt ?_
    obtain ⟨r, rfl⟩ : ∃ r, i = 2 * 2 ^ e + r := ⟨i - 2 * 2 ^ e, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have bd : ∀ r', r' ≤ r → St.Bd B (St.mk y' p xx 0 0 s e 0 (2 * (2 ^ e) ^ 2) k q r' 0 0 0) := by
      intro r' hr'; sbd
    rcases r with _ | _ | r
    · refine stepH_of (bd _ (by omega)) ?_; stp
      have : wAns N x mode s e (2 * 2 ^ e) = mode := by
        cases mode
        · simp [wAns]
        · simp only [wAns, if_true]; exact decide_eq_true (by omega)
      rw [this]; exact ans_halt (bd _ (by omega)) _
    · refine stepH_of (bd _ (by omega)) ?_; stp
      refine stepH_of (bd _ (by omega)) ?_; stp
      refine stepH_of (bd _ (by omega)) ?_; stp
      have : wAns N x mode s e (2 * 2 ^ e + 1) = true := by
        cases mode
        · simp [wAns]
        · simp only [wAns, if_true]; exact decide_eq_true (by omega)
      rw [this]; exact ans_halt (bd _ (by omega)) _
    · refine stepH_of (bd _ (by omega)) ?_; stp
      refine stepH_of (bd _ (by omega)) ?_; stp
      refine stepH_of (bd _ (by omega)) ?_; stp
      refine stepH_of (bd _ (by omega)) ?_; stp
      have h4 := le_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N)
        (y := pairEncode x β) (B := B) .M (St.mk y' p xx 0 0 s e 0 (2 * (2 ^ e) ^ 2) k q
          r 0 0 0) (bd r (by omega)) rfl
      regs [leReg, leYes, leNo] at h4
      have hk : 2 * 2 ^ e + (r + 1 + 1) - (2 * 2 ^ e + 2) = r := by omega
      by_cases h5 : 2 * (2 ^ e) ^ 2 ≤ r
      · rw [if_pos h5] at h4
        refine h4.halt ?_
        have bd' : St.Bd B (St.mk y' p xx 0 0 s e 0 (2 * (2 ^ e) ^ 2) k q r
            (min (2 * (2 ^ e) ^ 2) r) 0 0) := by
          have := bd r (by omega); simp only [St.Bd] at this ⊢; omega
        refine stepH_of bd' ?_; stp
        have h6 := sb_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N)
          (y := pairEncode x β) (B := B) .M (St.mk y' p xx 0 0 s e 0 (2 * (2 ^ e) ^ 2) k q
            r 0 0 0) (bd r (by omega))
        regs [sbReg, sbExit] at h6
        refine h6.halt ?_
        have h7 := tail_halt (a := a) (b := b) (f := f) (mode := mode) (o := orc N)
          (y := pairEncode x β) (B := B) (St.mk y' p xx 0 0 s e 0 0 k q
            (r - 2 * (2 ^ e) ^ 2) 0 0 0)
          (by have := bd r (by omega); simp only [St.Bd] at this ⊢; omega)
        simp only at h7
        convert h7 using 1
        simp only [wAns, tailVal]
        cases mode
        · simp only [Bool.false_eq_true, if_false]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hk, if_neg (by omega)]
          obtain ⟨w, hw⟩ : ∃ w, r - 2 * (2 ^ e) ^ 2 = w := ⟨_, rfl⟩
          rw [hw]
          rcases w with _ | _ | _ | _ | _ | w <;> simp [tailAns]
        · simp only [if_true]
          by_cases h8 : r - 2 * (2 ^ e) ^ 2 < 5
          · rw [dif_pos h8]
            have : 2 * 2 ^ e + (r + 1 + 1) < 2 * (2 ^ e) ^ 2 + 2 * 2 ^ e + 7 := by omega
            simp only [this, decide_true]
            obtain ⟨w, hw⟩ : ∃ w, r - 2 * (2 ^ e) ^ 2 = w := ⟨_, rfl⟩
            simp only [hw] at h8 ⊢
            rcases w with _ | _ | _ | _ | _ | w <;> simp [tailAns] at h8 ⊢
          · rw [dif_neg h8]
            have : ¬ 2 * 2 ^ e + (r + 1 + 1) < 2 * (2 ^ e) ^ 2 + 2 * 2 ^ e + 7 := by omega
            simp [this]
      · rw [if_neg h5] at h4
        refine h4.halt ?_
        have bd' : St.Bd B (St.mk y' p xx 0 0 s e 0 (2 * (2 ^ e) ^ 2) k q r
            (min (2 * (2 ^ e) ^ 2) r) 0 0) := by
          have := bd r (by omega); simp only [St.Bd] at this ⊢; omega
        refine stepH_of bd' ?_; stp
        have h6 := matrix_halt (a := a) (b := b) (f := f) (mode := mode) (B := B) N x β
          (St.mk y' p xx 0 0 s e 0 (2 * (2 ^ e) ^ 2) k q r 0 0 0) (bd r (by omega)) rfl rfl rfl rfl
        simp only at h6
        convert h6 using 1
        simp only [wAns]
        cases mode
        · simp only [Bool.false_eq_true, if_false]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hk, if_pos (by omega)]
        · simp only [if_true]
          have : 2 * 2 ^ e + (r + 1 + 1) < 2 * (2 ^ e) ^ 2 + 2 * 2 ^ e + 7 := by omega
          simp [this]
  · rw [if_neg h2] at h1
    refine h1.halt ?_
    have : wAns N x mode s e i = true := by
      cases mode
      · simp [wAns, show i < 2 * 2 ^ e by omega]
      · simp only [wAns, if_true]
        have : i < 2 * (2 ^ e) ^ 2 + 2 * 2 ^ e + 7 := by omega
        simp [this]
    rw [this]
    exact ans_halt (by have := hbd; simp only [St.Bd] at this ⊢; omega) _

end Complexity.PathHard
