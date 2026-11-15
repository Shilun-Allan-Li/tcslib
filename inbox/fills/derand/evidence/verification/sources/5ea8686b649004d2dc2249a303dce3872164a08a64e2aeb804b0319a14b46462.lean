/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine
import TCSlib.Complexity.SpaceComplexity.Codec.Parse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The parse, setup and decode phases of the `PATH` query machine

The first three phases of `Complexity.PathHard.A` on a query `y`:

* `parse_run` — measure `|y|` (`inputLength_loop`) and scan the aligned pair `⟨x, β⟩`
  (`alignedPair_loop`): a non-pair is rejected, a pair leaves the pointer at `2|x| + 2`;
* `setup_run` — recover `|x|`, count `ℓ = |bits (|x| + 1)|` (`Complexity.Codec.halvCount_loop`),
  compute the radius `aℓ` and the exponent `E = bℓ + f` (`registerScale_loop`,
  `Complexity.Codec.incChain`), and `2n = 2 ^ (E + 1)`, `2n² = 2 ^ (2E + 1)`, `4n²`
  (`shl_run`);
* `check_decode_run` — check that `β` is canonical and at most `|bits (4n²)|` letters long
  (`canonicalTail_loop`), and decode it (`boundedDecode_loop`).

Infrastructure for [AB09, §4.3, Theorem 4.18]; not itself a result of the book.

## Main definitions

* `Complexity.PathHard.setSt` — the register file after the setup.

## Main results

* `Complexity.PathHard.parse_run`, `setup_run`, `check_decode_run`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg

variable {a b f : ℕ} {mode : Bool} {B : ℕ} (N : FinNDTM Bool)

set_option hygiene false in
/-- Close a register bound of the setup, with the power identities `e0`, `e1`, `e2` in
context. -/
local macro "sbd2" : tactic =>
  `(tactic| (simp only [St.Bd, St.zero, shReg, St.toV_n, St.toV_m, St.toV_k, e0, e1, e2] <;>
    omega))

/-! ## Measuring and the pair scan -/

/-- **The parse phase**: from the start, a query `y` that is no pair is rejected; a pair
`⟨x, β⟩` brings the machine to `cp X` with `y = |y|` and `p = 2|x| + 2`.

**Proof sketch.** `inputLength_loop` counts `|y|`; `alignedPair_loop` (stride `1`, reading
through decider `0`) either fails, which leads to `ans false`, or stops past the separator. -/
theorem parse_run (y : List Bool) (hB : y.length ≤ B) :
    (pairDecode y = none → AHalt (A a b f mode) (orc N) y (GuardLe (A a b f mode) y B)
      (some .lenQ, St.zero.toV, none) false) ∧
    (∀ x β, y = pairEncode x β → AReach (A a b f mode) (orc N) y (GuardLe (A a b f mode) y B)
      (some .lenQ, St.zero.toV, none)
      (some (.cp .X), St.toV { St.zero with y := y.length, p := 2 * x.length + 2 }, none)) := by
  have h1 := inputLength_loop (A a b f mode) (orc N) y rY 1 .lenQ .lenI .scan rfl rfl
    (fun n _ => orc_len N y n) B hB St.zero.toV
    (fun r => by fin_cases r <;> simp [St.toV, St.zero]) (by simp [St.zero])
  regs at h1
  have h2 := alignedPair_loop (A a b f mode) (orc N) y rP rY 0 .scan .first .test .read
    (.ans false) (.cp .X) advF 1 B (by norm_num) (by decide) rfl rfl (fun _ => rfl)
    (fun _ => rfl) (fun k i hi => by cases (show i = 0 by omega); rfl)
    ⟨rfl, rfl, rfl, rfl⟩ y
    (St.toV { St.zero with y := y.length })
    (fun r => by fin_cases r <;> simp [St.toV, St.zero, hB]) (by simp [St.zero])
    (fun i _ => by simp [St.zero, orc_bit])
  constructor
  · intro hd
    rw [hd] at h2
    obtain ⟨t, ht, run⟩ := h2
    regs at run
    refine (h1.trans run).halt (ans_halt (by simp only [St.Bd, St.zero]; omega) false)
  · intro x β hy
    have hd : pairDecode y = some (x, β) := by rw [hy, pairDecode_pairEncode]
    rw [hd] at h2
    regs at h2
    refine (h1.trans h2).trans ?_
    simp only [St.zero, Nat.zero_add, Nat.one_mul]
    exact AReach.refl _

/-! ## The setup -/

/-- **The register file after the setup**: the query length `Y`, the pair pointer and
the width-check pointer `P`, `|x| = X`, radius `s`, exponent `E`, `2n`, `2n²`, the cap
`4n²`. -/
def setSt (Y P X s E : ℕ) : St :=
  ⟨Y, P, X, 0, 0, s, E, 2 * 2 ^ E, 2 * (2 ^ E) ^ 2, 4 * (2 ^ E) ^ 2, P, 0, 0, 0, 0⟩

/-- **The setup**: from `cp X` with `y = Y`, `p = 2X + 2`, the machine reaches the width check
with the register file `setSt Y (2X + 2) X (a ℓ) E`, where `ℓ = |bits (X + 1)|` and
`E = b ℓ + f`.

**Proof sketch.** `x := p - 2` halved; `t := x + 1`; count its bits into `c`
(`halvCount_loop`); copy `c` into `t`; scale `t` into `s` by `a` and `c` into `e` by `b`
(`registerScale_loop`); add `f` (`incChain`); `n := 2 ^ (e + 1)`, `m := n · 2 ^ e`,
`k := 2m` by shift loops (`sh_run`); `q := p`. -/
theorem setup_run (y : List Bool) (Y X : ℕ) (hab : a ≤ b) (hX : 2 * X + 2 ≤ Y)
    (hB : Y + 8 * (2 ^ (b * ell X + f)) ^ 2 ≤ B) :
    AReach (A a b f mode) (orc N) y (GuardLe (A a b f mode) y B)
      (some (.cp .X), St.toV { St.zero with y := Y, p := 2 * X + 2 }, none)
      (some (.tt true), (setSt Y (2 * X + 2) X (a * ell X) (b * ell X + f)).toV, none) := by
  set ℓ := ell X with hℓ
  set E := b * ℓ + f with hE
  have hEp : E < 2 ^ E := Nat.lt_two_pow_self
  have hp1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hsq : 2 ^ E ≤ (2 ^ E) ^ 2 := by nlinarith
  have hℓX : ℓ ≤ Y := by
    have h1 : 2 ^ ℓ ≤ 2 * (X + 1) := two_pow_ell_le X
    have h2 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    omega
  have e0 : 1 * 2 ^ (E + 1) = 2 * 2 ^ E := by ring
  have e1 : 2 * 2 ^ E * 2 ^ E = 2 * (2 ^ E) ^ 2 := by ring
  have e2 : 2 * (2 ^ E) ^ 2 * 2 ^ 1 = 4 * (2 ^ E) ^ 2 := by ring
  have haE : a * ℓ ≤ E := by
    have : a * ℓ ≤ b * ℓ := Nat.mul_le_mul_right _ hab
    omega
  -- `x := p`
  have h1 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .X { St.zero with y := Y, p := 2 * X + 2 } (by simp only [St.Bd, St.zero]; omega)
    (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h1
  refine h1.trans ?_
  refine step_of (by simp only [St.Bd, St.zero]; omega) ?_; stp
  refine step_of (by simp only [St.Bd, St.zero]; omega) ?_; stp
  refine step_of (by simp only [St.Bd, St.zero]; omega) ?_; stp
  have ex : (2 * X + 2 - 1 - 1) / 2 = X := by omega
  simp only [ex]
  -- `t := x + 1`
  have h2 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .T { St.zero with y := Y, p := 2 * X + 2, x := X } (by simp only [St.Bd, St.zero]; omega)
    (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h2
  refine h2.trans ?_
  refine step_of (by simp only [St.Bd, St.zero]; omega) ?_; stp
  -- `c := ℓ`
  have h3 := Codec.halvCount_loop (A a b f mode) (orc N) y rT rC (by decide) .hcT .hcH .hcB
    (.cp .TC) rfl rfl rfl B (St.toV { St.zero with y := Y, p := 2 * X + 2, x := X, t := X + 1 })
    (St.Bd.toV (by simp only [St.Bd, St.zero]; omega))
    (by have h : (Nat.bits (X + 1)).length = ℓ := rfl
        simp only [St.toV_c, St.toV_t, St.zero]; omega)
  regs at h3
  refine h3.trans ?_
  simp only [St.zero, Nat.zero_add, show (Nat.bits (X + 1)).length = ℓ from rfl]
  -- `t := c`
  have h4 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .TC { St.zero with y := Y, p := 2 * X + 2, x := X, c := ℓ }
    (by simp only [St.Bd, St.zero]; omega) (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h4
  refine h4.trans ?_
  -- `s := a ℓ`
  have h5 := registerScale_loop (A a b f mode) (orc N) y rT rS (by decide) .sS .sSD .sE sSinc a
    rfl rfl (fun i hi => by simp only [sSinc, dif_pos hi]; rfl)
    (by simp [sSinc]) B (St.toV { St.zero with y := Y, p := 2 * X + 2, x := X, c := ℓ, t := ℓ })
    (St.Bd.toV (by simp only [St.Bd, St.zero]; omega)) (by simp [St.zero]; omega)
  regs at h5
  refine h5.trans ?_
  -- `e := b ℓ`
  have h6 := registerScale_loop (A a b f mode) (orc N) y rC rE (by decide) .sE .sED (eInc 0)
    sEinc b rfl rfl (fun i hi => by simp only [sEinc, dif_pos hi]; rfl)
    (by simp [sEinc]) B
    (St.toV { St.zero with y := Y, p := 2 * X + 2, x := X, c := ℓ, t := 0, s := 0 + a * ℓ })
    (St.Bd.toV (by simp only [St.Bd, St.zero]; omega)) (by simp [St.zero]; omega)
  regs at h6
  refine h6.trans ?_
  -- `e := b ℓ + f`
  have h7 := Codec.incChain (A a b f mode) (orc N) y rE eInc f B
    (fun i hi => by simp only [eInc, dif_pos hi]; rfl)
    (St.toV { St.zero with y := Y, p := 2 * X + 2, x := X, c := 0, t := 0, s := 0 + a * ℓ,
                           e := 0 + b * ℓ }) (St.Bd.toV (by simp only [St.Bd, St.zero]; omega))
    (by simp [St.zero]; omega)
  regs at h7
  rw [show eInc (a := a) (b := b) (f := f) f = .cp .CN by simp [eInc]] at h7
  refine h7.trans ?_
  simp only [St.zero, Nat.zero_add]
  -- `n := 2 ^ (e + 1)`
  have h8 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .CN { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E }
    (by simp only [St.Bd, St.zero]; omega) (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h8
  refine h8.trans ?_
  refine step_of (by simp only [St.Bd, St.zero]; omega) ?_; stp
  refine step_of (by simp only [St.Bd, St.zero]; omega) ?_; stp
  have h9 := sh_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .N { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, c := E + 1, n := 1 }
    (by simp only [St.Bd, St.zero]; omega) rfl (by sbd2)
  regs [shReg, shExit] at h9
  refine h9.trans ?_
  -- `m := n · 2 ^ e`
  have h10 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .MN { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, n := 1 * 2 ^ (E + 1) }
    (by sbd2) (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h10
  refine h10.trans ?_
  have h11 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .CM { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, n := 1 * 2 ^ (E + 1),
                       m := 1 * 2 ^ (E + 1) }
    (by sbd2) (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h11
  refine h11.trans ?_
  have h12 := sh_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .M { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, n := 1 * 2 ^ (E + 1),
                      m := 1 * 2 ^ (E + 1), c := E }
    (by sbd2) rfl
    (by sbd2)
  regs [shReg, shExit] at h12
  refine h12.trans ?_
  -- `k := 2m`
  have h13 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .KM { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, n := 1 * 2 ^ (E + 1),
                       m := 1 * 2 ^ (E + 1) * 2 ^ E }
    (by sbd2) (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h13
  refine h13.trans ?_
  refine step_of (by sbd2) ?_; stp
  have h14 := sh_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .K { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, n := 1 * 2 ^ (E + 1),
                      m := 1 * 2 ^ (E + 1) * 2 ^ E, k := 1 * 2 ^ (E + 1) * 2 ^ E, c := 1 }
    (by sbd2) rfl
    (by sbd2)
  regs [shReg, shExit] at h14
  refine h14.trans ?_
  -- `q := p`
  have h15 := cp_run (a := a) (b := b) (f := f) (mode := mode) (o := orc N) (y := y) (B := B)
    .QP { St.zero with y := Y, p := 2 * X + 2, x := X, s := a * ℓ, e := E, n := 1 * 2 ^ (E + 1),
                       m := 1 * 2 ^ (E + 1) * 2 ^ E, k := 1 * 2 ^ (E + 1) * 2 ^ E * 2 ^ 1 }
    (by sbd2) (by simp [cpDst, cpSrc, St.zero])
  regs [cpDst, cpSrc, cpNext] at h15
  refine reach_of_eq h15 ?_
  simp only [setSt, St.zero, e0, e1, e2]

/-! ## The width check and decoding -/

/-- **The width check and decoding**: on a query `y = ⟨x, β⟩`, from the width check with
`y = |y|`, `p = q = 2|x| + 2`, `i = d = 0` and a cap `k ≥ 1` (with `2k ≤ B`): if `β` is a
canonical word of at most `|bits k|` letters, the machine reaches the walk with `i` the value
of `β` (and `y := p`; `q`, `k` changed); otherwise it rejects.

**Proof sketch.** `canonicalTail_loop` (stride `1`) decides the width and canonicity
check; on success `boundedDecode_loop` decodes `β` from its end down to `p`, with values at
most `2k` (`Complexity.Codec.bitsVal_le_of_width`). The registers outside each loop are
unchanged (the loops' frame clauses). -/
theorem check_decode_run (x β y : List Bool) (hy0 : y = pairEncode x β) (st : St)
    (hbd : st.Bd B) (hy : st.y = y.length) (hp : st.p = 2 * x.length + 2) (hq : st.q = st.p)
    (hi : st.i = 0) (hd : st.d = 0) (hk : 1 ≤ st.k) (hkB : 2 * st.k ≤ B) :
    (β.length ≤ (Nat.bits st.k).length ∧ Canon β ∧ ∃ q' k' : ℕ, q' ≤ B ∧ k' ≤ B ∧
      AReach (A a b f mode) (orc N) y (GuardLe (A a b f mode) y B)
        (some (.tt true), st.toV, none)
        (some (.le .N 0), St.toV { st with y := st.p, i := LogProg.bitsVal β, q := q', k := k' },
          none)) ∨
    (¬ (β.length ≤ (Nat.bits st.k).length ∧ Canon β) ∧
      AHalt (A a b f mode) (orc N) y (GuardLe (A a b f mode) y B)
        (some (.tt true), st.toV, none) false) := by
  have hylen : y.length = 2 * x.length + 2 + β.length := by rw [hy0, length_pairEncode]
  have hread : ∀ i, orc N 0 (pairEncode y (Nat.bits (2 * x.length + 2 + i))) = β.getD i false := by
    intro i; rw [orc_bit, hy0, Codec.pe_getD_snd]
  obtain ⟨v', hv', -, hframe, run⟩ := canonicalTail_loop (A a b f mode) (orc N) y rQ rY rK
    (by decide) (by decide) (by decide) 0 .tt .tc .tr (.ans false) .dT .th tAdv 1 B (by norm_num)
    (fun _ => rfl) rfl rfl (fun _ => rfl)
    (fun c i hi => by cases (show i = 0 by omega); rfl)
    (fun _ => rfl) β true st.toV hbd.toV (by simp only [St.toV_y, St.toV_q]; omega)
    (fun i _ => by simp only [St.toV_q, hq, hp, Nat.one_mul]; exact hread i)
  have hv'eq : v' = St.toV { st with q := v' rQ, k := v' rK } := St.eq_qk st v' hframe
  rw [hv'eq] at run hv'
  simp only [St.toV_k] at run
  by_cases ok : β.length ≤ (Nat.bits st.k).length ∧ β.getLastD true = true
  · rw [if_pos ok.1, if_pos ok.2] at run
    left
    refine ⟨ok.1, Codec.canon_of_getLastD ok.2, v' rQ, v' rK, hv' rQ, hv' rK, run.trans ?_⟩
    obtain ⟨w', hw', hwY, hwI, hwD, hframe2, run2⟩ := boundedDecode_loop (A a b f mode) (orc N) y
      rY rP rI rD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0
      .dT .dD .dR (.le .N 0) .dC .dB .dL .dS .dK .dA dInc rfl rfl rfl (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun c i hi => by simp only [dInc, dif_pos hi]; rfl) (fun _ => by simp [dInc])
      (fun _ => rfl) β B (fun i _ => (Codec.bitsVal_le_of_width β st.k hk ok.1 i).trans hkB)
      β.length le_rfl _ hv' (by simp only [St.toV_y, St.toV_p]; omega)
      (by simp [hi, LogProg.bitsVal]) (by simp [hd])
      (fun i _ => by simp only [St.toV_p, hp]; exact hread i)
    refine reach_of_eq run2 ?_
    rw [St.eq_yid _ w' hframe2, hwY, hwI, hwD]
    simp only [St.toV_p, hd]
  · right
    refine ⟨fun h => ok ⟨h.1, Codec.getLastD_of_canon h.2⟩, ?_⟩
    have e : (if β.length ≤ (Nat.bits st.k).length then
        if β.getLastD true = true then (Lb.dT : Lb a b f) else .ans false else .ans false) =
        .ans false := by
      split_ifs with h1 h2 <;> first | rfl | exact absurd ⟨h1, h2⟩ ok
    rw [e] at run
    exact run.halt (ans_halt (St.Bd.of_toV hv') false)

end Complexity.PathHard
