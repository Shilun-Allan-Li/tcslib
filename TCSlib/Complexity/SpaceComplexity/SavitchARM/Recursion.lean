/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Run
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The midpoint recursion of the Savitch register machine

The recursive part of `Complexity.LogProg.SavitchARM.A` computes midpoint reachability:
started at label `cl` on a node `(U, V)` at level `I = i`, with any stack contents of the
right size below it, the machine returns at label `rt b` with `b` the truth value of
`Reach (2 ^ w) R i U V` — with the same registers, except the scratch midpoint register `M`
(`Complexity.LogProg.SavitchARM.call_spec`). Here `R` is the step relation answered by
decider `3` on codes at radius `s`.

The proof is an induction on the level, mirroring the recursion of [AB09, §4.2.1, proof of
Theorem 4.14]: at a positive level the midpoint loop (`loop_spec`) descends into the first
half (`desc1`, pushing `(V, 0)`), and, if that half is reachable, into the second half
(`desc2`, pushing `(U, 1)`); every return pops the frame it pushed (`pop_run`) and dispatches
on its phase bit. The stack invariant `Complexity.LogProg.SavitchARM.Inv` bounds the
`w`-bit-digit stack `SE` by `2 ^ (w (w - i))` and the phase stack `SP` by `2 ^ (w - i)`, so
every register stays below `2 ^ (w · w)`.

## Main definitions

* `Complexity.LogProg.SavitchARM.Rel` — the step relation read from the oracle.
* `Complexity.LogProg.SavitchARM.Inv` — the register invariant at a level.

## Main results

* `Complexity.LogProg.SavitchARM.call_spec` — the recursion computes `Reach`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

/-- **The step relation read from the oracle**: decider `3` accepts
`⟨x, ⟨bits u, ⟨bits v, bits s⟩⟩⟩`. -/
def Rel (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s u v : ℕ) : Prop :=
  orc 3 (pairEncode x (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) = true

/-- **The register invariant at level `i`**: the setup registers and the scratch registers
are clear, the radius, width and code bound are in place, the node's codes are below
`2 ^ w`, the midpoint is at most `2 ^ w`, and the two stacks hold at most `w - i` frames. -/
structure Inv (s w i : ℕ) (st : St) : Prop where
  /-- the input-length counter is clear -/
  hn : st.n = 0
  /-- the base register is clear -/
  ha : st.a = 0
  /-- the exponent counter is clear -/
  hX : st.X = 0
  /-- the power accumulator is clear -/
  hP : st.P = 0
  /-- the scratch register `T` is clear -/
  hT : st.T = 0
  /-- the scratch register `Z` is clear -/
  hZ : st.Z = 0
  /-- the loop counter is clear -/
  hC : st.C = 0
  /-- the scratch register `Q` is clear -/
  hQ : st.Q = 0
  /-- the popped-endpoint register is clear -/
  hE : st.E = 0
  /-- the radius is `s` -/
  hs : st.s = s
  /-- the width is `w` -/
  hw : st.w = w
  /-- the code bound is `2 ^ w` -/
  hK : st.K = 2 ^ w
  /-- the source code is below `2 ^ w` -/
  hU : st.U < 2 ^ w
  /-- the target code is below `2 ^ w` -/
  hV : st.V < 2 ^ w
  /-- the midpoint is at most `2 ^ w` -/
  hM : st.M ≤ 2 ^ w
  /-- the level is `i` -/
  hI : st.I = i
  /-- the endpoint stack holds at most `w - i` digits of `w` bits -/
  hSE : st.SE < 2 ^ (w * (w - i))
  /-- the phase stack holds at most `w - i` bits -/
  hSP : st.SP < 2 ^ (w - i)

/-- The basic size facts: `w ≤ 2 ^ w ≤ 2 ^ (w · w)`. -/
lemma size_facts (w : ℕ) : w < 2 ^ w ∧ 2 ^ w ≤ 2 ^ (w * w) :=
  ⟨Nat.lt_two_pow_self, Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self w)⟩

/-- **The invariant bounds the registers** by `2 ^ (w · w)`. -/
lemma Inv.bd {s w i : ℕ} {st : St} (h : Inv s w i st) (hsw : s ≤ w) (hi : i ≤ w) :
    st.Bd (2 ^ (w * w)) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have g1 : 2 ^ (w * (w - i)) ≤ 2 ^ (w * w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have g2 : 2 ^ (w - i) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h.hn; have := h.ha; have := h.hX; have := h.hP; have := h.hT; have := h.hZ
  have := h.hC; have := h.hQ; have := h.hE; have := h.hs; have := h.hw; have := h.hK
  have := h.hU; have := h.hV; have := h.hM; have := h.hI; have := h.hSE; have := h.hSP
  simp only [St.Bd]
  omega

/-- **Pushing a digit keeps the stack within one more frame**: `SE < 2 ^ (w (w - (i + 1)))`
and `v < 2 ^ w` give `SE · 2 ^ w + v < 2 ^ (w (w - i))`. -/
lemma push_lt {w i SE v : ℕ} (hi : i + 1 ≤ w) (hSE : SE < 2 ^ (w * (w - (i + 1))))
    (hv : v < 2 ^ w) : SE * 2 ^ w + v < 2 ^ (w * (w - i)) := by
  have e : w * (w - i) = w * (w - (i + 1)) + w := by
    rw [show w - i = w - (i + 1) + 1 by omega, Nat.mul_succ]
  rw [e, pow_add]
  have : (SE + 1) * 2 ^ w ≤ 2 ^ (w * (w - (i + 1))) * 2 ^ w :=
    Nat.mul_le_mul_right _ hSE
  rw [Nat.add_mul, one_mul] at this
  omega

/-- Pushing a phase bit keeps the phase stack within one more frame. -/
lemma pushP_lt {w i SP : ℕ} (hi : i + 1 ≤ w) (hSP : SP < 2 ^ (w - (i + 1))) :
    2 * SP + 1 < 2 ^ (w - i) := by
  rw [show w - i = w - (i + 1) + 1 by omega, pow_succ]
  omega

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s w : ℕ}

open Classical in
/-- **The base case**: at level `0` the machine answers `U = V ∨ R U V`.

**Proof sketch.** `cl` sees `I = 0` and calls decider `3` on `⟨x, ⟨bits U, ⟨bits V, bits s⟩⟩⟩`;
on a negative answer it compares `U` with `V`. -/
theorem base_spec (hsw : s ≤ w) (st : St) (h : Inv s w 0 st) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .cl, st.toV, none)
      (some (.rt (decide (Reach (2 ^ w) (Rel orc x s) 0 st.U st.V))), st.toV, none) := by
  have hbd := h.bd hsw (Nat.zero_le _)
  refine step_of hbd ?_
  regs [astep, A, h.hI, ↓reduceIte]
  refine step_of hbd ?_
  simp only [astep, A, vword_whole₃]
  regs [h.hs]
  by_cases hr : Rel orc x s st.U st.V
  · have hr' : orc 3 (pairEncode x (pairEncode (Nat.bits st.U)
        (pairEncode (Nat.bits st.V) (Nat.bits s)))) = true := hr
    rw [if_pos hr', decide_eq_true (show Reach (2 ^ w) (Rel orc x s) 0 st.U st.V from Or.inr hr)]
    exact AReach.refl _
  · have hr' : ¬ orc 3 (pairEncode x (pairEncode (Nat.bits st.U)
        (pairEncode (Nat.bits st.V) (Nat.bits s)))) = true := hr
    rw [if_neg hr']
    refine step_of hbd ?_
    regs [astep, A]
    by_cases he : st.U = st.V
    · rw [if_pos he, decide_eq_true (show Reach (2 ^ w) (Rel orc x s) 0 st.U st.V from Or.inl he)]
      exact AReach.refl _
    · rw [if_neg he, decide_eq_false (show ¬ Reach (2 ^ w) (Rel orc x s) 0 st.U st.V by
        rintro (h1 | h1) <;> contradiction)]
      exact AReach.refl _

/-- Close a register-file bound from the unfolded bounds in context. -/
scoped macro "bdt" : tactic => `(tactic| (simp only [St.Bd]; omega))

variable (E orc x s w) in
open Classical in
/-- **The recursion is correct at level `i`**: from `cl` on any register file meeting the
invariant at level `i`, the machine reaches `rt b`, `b` the truth value of
`Reach (2 ^ w) R i U V`, changing only the midpoint register (to a value at most `2 ^ w`). -/
def CallOK (i : ℕ) : Prop :=
  ∀ st, Inv s w i st → ∃ M', M' ≤ 2 ^ w ∧
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .cl, st.toV, none)
      (some (.rt (decide (Reach (2 ^ w) (Rel orc x s) i st.U st.V))),
        St.toV { st with M := M' }, none)

open Classical in
/-- **The first descent**: from `loop` at level `i + 1` with midpoint `m = M < 2 ^ w`, the
machine pushes `(V, 0)`, evaluates the first half `(U, m)` at level `i`, pops the frame, and
reaches `cp (push true)` if the first half is reachable and `a0F` otherwise, with `V = m`
and the popped endpoint in `E`.

**Proof sketch.** `pushV_run`, the move of `M` into `V` and the decrement of `I`; the
recursion at level `i` (`CallOK`); at `rt b` the level is below `w`, so `pop_run` restores
`SE` and returns the saved `V` in `E`; `I` is incremented, the even phase stack selects
`h0`, which halves it back. -/
theorem desc1 (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (IH : CallOK E orc x s w i) (st : St)
    (h : Inv s w (i + 1) st) (hm : st.M < 2 ^ w) :
    ∃ M1, M1 ≤ 2 ^ w ∧ AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .loop, st.toV, none)
      (some (if decide (Reach (2 ^ w) (Rel orc x s) i st.U st.M) then .cp (.push true) 0
        else .a0F), St.toV { st with V := st.M, M := M1, E := st.V }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hbd := h.bd hsw hi
  have hSE1 := push_lt hi h.hSE h.hV
  have hSP1 := pushP_lt hi h.hSP
  have g1 : 2 ^ (w * (w - i)) ≤ 2 ^ (w * w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have g2 : 2 ^ (w - i) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : Inv s w i
      { st with SE := st.SE * 2 ^ w + st.V, V := st.M, SP := 2 * st.SP, M := 0, I := i } :=
    ⟨h.hn, h.ha, h.hX, h.hP, h.hT, h.hZ, h.hC, h.hQ, h.hE, h.hs, h.hw, h.hK, h.hU, hm,
      Nat.zero_le _, rfl, hSE1, by show 2 * st.SP < 2 ^ (w - i); omega⟩
  obtain ⟨M1, hM1, hc⟩ := IH _ h3
  dsimp only at hc
  refine ⟨M1, hM1, ?_⟩
  have hw := h.hw
  -- `loop`: the midpoint is below `K`
  refine step_of hbd ?_
  regs [astep, A, if_neg (show st.M ≠ st.K by rw [h.hK]; exact hm.ne)]
  -- push `(V, 0)`
  refine (pushV_run st h.hC h.hT h.hZ hbd (by rw [hw]; omega) (by omega)).trans ?_
  have hbd1 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE * 2 ^ st.w + st.V, V := 0, SP := 2 * st.SP } := by
    have := hbd; simp only [St.Bd] at this ⊢; rw [hw]; omega
  have hMB : st.M ≤ 2 ^ (w * w) := by omega
  refine (mv_run .descM _ hbd1 (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  have hbd2 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE * 2 ^ st.w + st.V, V := st.M, SP := 2 * st.SP, M := 0 } := by
    have := hbd; simp only [St.Bd] at this ⊢; rw [hw]; omega
  refine step_of hbd2 ?_
  regs [astep, A]
  refine cont (by ext <;> simp [hw, h.hI]) (hc.trans ?_)
  -- `rt b`: not the root, pop the frame
  have hbd4 := (h3.bd hsw (by omega))
  have hbd4' : St.Bd (2 ^ (w * w))
      { st with SE := st.SE * 2 ^ w + st.V, V := st.M, SP := 2 * st.SP, M := M1, I := i } := by
    simp only [St.Bd] at hbd4 ⊢; omega
  refine step_of hbd4' ?_
  regs [astep, A, if_neg (show i ≠ st.w by omega)]
  refine (pop_run _
    { st with SE := st.SE * 2 ^ w + st.V, V := st.M, SP := 2 * st.SP, M := M1, I := i }
    st.SE st.V h.hC h.hT h.hZ h.hQ h.hE hbd4' (by simp [hw]) (by simp [hw]; exact h.hV)).trans ?_
  have hbd5 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE, V := st.M, SP := 2 * st.SP, M := M1, I := i, E := st.V } := by
    have := Nat.le_mul_of_pos_right st.SE (Nat.two_pow_pos w)
    simp only [St.Bd] at hbd4 ⊢; have := h.hV; omega
  refine step_of hbd5 ?_
  regs [astep, A]
  have hbd6 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE, V := st.M, SP := 2 * st.SP, M := M1, I := i + 1, E := st.V } := by
    simp only [St.Bd] at hbd5 ⊢; omega
  refine step_of hbd6 ?_
  regs [astep, A, Nat.mul_mod_right, zero_ne_one, if_false]
  refine step_of hbd6 ?_
  regs [astep, A]
  refine reach_of_eq (AReach.refl _) ?_
  congr 3
  ext <;> simp [h.hI]

open Classical in
/-- **The second descent**: from `cp (push true)` after a reachable first half (`V = m`,
`E` the saved target), the machine pushes `(U, 1)`, evaluates the second half `(m, V)` at
level `i`, pops the frame, and reaches `a1T` if the second half is reachable and `a1F`
otherwise, with `U = m` and the saved source in `E`.

**Proof sketch.** `pushU_run`, the increment of the phase stack, the moves `V → U`,
`E → V` and the decrement of `I`; the recursion at level `i`; `pop_run` restores `SE` and
returns the saved `U` in `E`; the odd phase stack selects `h1`, which halves it back. -/
theorem desc2 (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (IH : CallOK E orc x s w i) (st : St)
    (h : Inv s w (i + 1) st) (hm : st.M < 2 ^ w) (M1 : ℕ) (hM1 : M1 ≤ 2 ^ w) :
    ∃ M2, M2 ≤ 2 ^ w ∧ AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some (.cp (.push true) 0), St.toV { st with V := st.M, M := M1, E := st.V }, none)
      (some (if decide (Reach (2 ^ w) (Rel orc x s) i st.M st.V) then .a1T else .a1F),
        St.toV { st with U := st.M, M := M2, E := st.U }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hbd := h.bd hsw hi
  have hB := hbd
  simp only [St.Bd] at hB
  have hSE1 := push_lt hi h.hSE h.hU
  have hSP1 := pushP_lt hi h.hSP
  have g1 : 2 ^ (w * (w - i)) ≤ 2 ^ (w * w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have g2 : 2 ^ (w - i) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle := Nat.le_mul_of_pos_right st.SE (Nat.two_pow_pos w)
  have h3 : Inv s w i
      { st with SE := st.SE * 2 ^ w + st.U, U := st.M, SP := 2 * st.SP + 1, M := M1, I := i } :=
    ⟨h.hn, h.ha, h.hX, h.hP, h.hT, h.hZ, h.hC, h.hQ, h.hE, h.hs, h.hw, h.hK, hm, h.hV,
      hM1, rfl, hSE1, hSP1⟩
  obtain ⟨M2, hM2, hc⟩ := IH _ h3
  dsimp only at hc
  refine ⟨M2, hM2, ?_⟩
  have hw := h.hw
  have hV := h.hV
  have hU := h.hU
  have hSEw : st.SE * 2 ^ st.w = st.SE * 2 ^ w := by rw [hw]
  -- push `(U, 1)`
  refine (pushU_run { st with V := st.M, M := M1, E := st.V } h.hC h.hT h.hZ (by bdt)
    (by show st.SE * 2 ^ st.w + st.U ≤ _; rw [hw]; omega)
    (by show 2 * st.SP ≤ _; omega)).trans ?_
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine (mv_run .a0T1 _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine (mv_run .a0T2 _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine cont (by ext <;> simp [hw, h.hI, h.hE]) (hc.trans ?_)
  -- `rt b`: not the root, pop the frame
  have hB3 := h3.bd hsw (by omega)
  simp only [St.Bd] at hB3
  refine step_of (by bdt) ?_
  regs [astep, A, if_neg (show i ≠ st.w by omega)]
  refine (pop_run _
    { st with SE := st.SE * 2 ^ w + st.U, U := st.M, SP := 2 * st.SP + 1, M := M2, I := i }
    st.SE st.U h.hC h.hT h.hZ h.hQ h.hE (by bdt) (by simp [hw]) (by simp [hw]; exact hU)).trans ?_
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine step_of (by bdt) ?_
  regs [astep, A, Nat.mul_add_mod, if_true]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (AReach.refl _) ?_
  congr 3
  ext <;> simp [h.hI]
  omega

/-- **The tail after an unreachable first half**: from `a0F`, the machine sets `M := V + 1`,
moves the saved target back into `V`, and returns to `loop`.

**Proof sketch.** A clear, two moves and an increment. -/
theorem tail0F (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (st : St) (h : Inv s w (i + 1) st)
    (hm : st.M < 2 ^ w) (M1 : ℕ) (hM1 : M1 ≤ 2 ^ w) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .a0F, St.toV { st with V := st.M, M := M1, E := st.V }, none)
      (some .loop, St.toV { st with M := st.M + 1 }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hB := h.bd hsw hi
  simp only [St.Bd] at hB
  have hV := h.hV
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine (mv_run .a0FM _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (mv_run .a0FV _ (by bdt) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  congr 3
  ext <;> simp [h.hE]

/-- **The tail after a reachable second half**: from `a1T`, the machine moves the saved
source back into `U` and answers `true`.

**Proof sketch.** A clear and a move. -/
theorem tail1T (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (st : St) (h : Inv s w (i + 1) st)
    (M2 : ℕ) (hM2 : M2 ≤ 2 ^ w) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .a1T, St.toV { st with U := st.M, M := M2, E := st.U }, none)
      (some (.rt true), St.toV { st with M := M2 }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hB := h.bd hsw hi
  simp only [St.Bd] at hB
  have hU := h.hU
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (mv_run .a1TU _ (by bdt) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  congr 3
  ext <;> simp [h.hE]

/-- **The tail after an unreachable second half**: from `a1F`, the machine sets
`M := U + 1`, moves the saved source back into `U`, and returns to `loop`.

**Proof sketch.** A clear, two moves and an increment. -/
theorem tail1F (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (st : St) (h : Inv s w (i + 1) st)
    (hm : st.M < 2 ^ w) (M2 : ℕ) (hM2 : M2 ≤ 2 ^ w) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .a1F, St.toV { st with U := st.M, M := M2, E := st.U }, none)
      (some .loop, St.toV { st with M := st.M + 1 }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hB := h.bd hsw hi
  simp only [St.Bd] at hB
  have hU := h.hU
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine (mv_run .a1FM _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (mv_run .a1FU _ (by bdt) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  congr 3
  ext <;> simp [h.hE]

/-- The invariant does not constrain the midpoint beyond `M ≤ 2 ^ w`. -/
lemma Inv.setM {s w i : ℕ} {st : St} (h : Inv s w i st) {M' : ℕ} (hM : M' ≤ 2 ^ w) :
    Inv s w i { st with M := M' } :=
  ⟨h.hn, h.ha, h.hX, h.hP, h.hT, h.hZ, h.hC, h.hQ, h.hE, h.hs, h.hw, h.hK, h.hU, h.hV, hM,
    h.hI, h.hSE, h.hSP⟩

/-- Skipping a failing candidate does not change a bounded search. -/
lemma exists_shift {R₁ R₂ : ℕ → Prop} {a K : ℕ} (h : ¬ (R₁ a ∧ R₂ a)) :
    (∃ m, a + 1 ≤ m ∧ m < K ∧ R₁ m ∧ R₂ m) ↔ (∃ m, a ≤ m ∧ m < K ∧ R₁ m ∧ R₂ m) := by
  constructor
  · rintro ⟨m, h1, h2, h3⟩
    exact ⟨m, by omega, h2, h3⟩
  · rintro ⟨m, h1, h2, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact absurd h3 h
    · exact ⟨m, h1, h2, h3⟩

open Classical in
/-- **The midpoint loop**: from `loop` at level `i + 1` with midpoint `M`, the machine
answers at `rt b` whether some `m` with `M ≤ m < 2 ^ w` has both halves reachable at level
`i`, changing only `M`.

**Proof sketch.** Induction on `2 ^ w - M`. At `M = 2 ^ w` the machine answers `false`.
Below, the first descent (`desc1`) evaluates the first half; if it fails, `tail0F` moves to
`M + 1`; otherwise the second descent (`desc2`) evaluates the second half, and `tail1T`
answers `true` or `tail1F` moves to `M + 1`. Moving past a failing candidate leaves the
answer unchanged (`exists_shift`). -/
theorem loop_spec (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (IH : CallOK E orc x s w i) :
    ∀ k (st : St), Inv s w (i + 1) st → st.M + k = 2 ^ w → ∃ M', M' ≤ 2 ^ w ∧
      AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .loop, st.toV, none)
        (some (.rt (decide (∃ m, st.M ≤ m ∧ m < 2 ^ w ∧ Reach (2 ^ w) (Rel orc x s) i st.U m ∧
          Reach (2 ^ w) (Rel orc x s) i m st.V))), St.toV { st with M := M' }, none) := by
  intro k
  induction k with
  | zero =>
    intro st h hk
    refine ⟨st.M, h.hM, ?_⟩
    refine step_of (h.bd hsw hi) ?_
    regs [astep, A, if_pos (show st.M = st.K by rw [h.hK]; omega)]
    rw [decide_eq_false (by rintro ⟨m, h1, h2, -⟩; omega)]
    exact AReach.refl _
  | succ k ih =>
    intro st h hk
    have hm : st.M < 2 ^ w := by omega
    have hnext := h.setM (M' := st.M + 1) (by omega)
    obtain ⟨M1, hM1, h1⟩ := desc1 hsw i hi IH st h hm
    by_cases r1 : Reach (2 ^ w) (Rel orc x s) i st.U st.M
    · simp only [r1, decide_true, if_true] at h1
      obtain ⟨M2, hM2, h2⟩ := desc2 hsw i hi IH st h hm M1 hM1
      by_cases r2 : Reach (2 ^ w) (Rel orc x s) i st.M st.V
      · simp only [r2, decide_true, if_true] at h2
        refine ⟨M2, hM2, ?_⟩
        rw [decide_eq_true ⟨st.M, le_rfl, hm, r1, r2⟩]
        exact h1.trans (h2.trans (tail1T hsw i hi st h M2 hM2))
      · simp only [r2, decide_false, Bool.false_eq_true, if_false] at h2
        obtain ⟨M', hM', h3⟩ := ih _ hnext (by show st.M + 1 + k = 2 ^ w; omega)
        dsimp only at h3
        have e := exists_shift (R₁ := fun m => Reach (2 ^ w) (Rel orc x s) i st.U m)
          (R₂ := fun m => Reach (2 ^ w) (Rel orc x s) i m st.V) (a := st.M) (K := 2 ^ w)
          (fun hh => r2 hh.2)
        beta_reduce at e
        rw [decide_eq_decide.mpr e] at h3
        exact ⟨M', hM', h1.trans (h2.trans ((tail1F hsw i hi st h hm M2 hM2).trans h3))⟩
    · simp only [r1, decide_false, Bool.false_eq_true, if_false] at h1
      obtain ⟨M', hM', h3⟩ := ih _ hnext (by show st.M + 1 + k = 2 ^ w; omega)
      dsimp only at h3
      have e := exists_shift (R₁ := fun m => Reach (2 ^ w) (Rel orc x s) i st.U m)
        (R₂ := fun m => Reach (2 ^ w) (Rel orc x s) i m st.V) (a := st.M) (K := 2 ^ w)
        (fun hh => r1 hh.1)
      beta_reduce at e
      rw [decide_eq_decide.mpr e] at h3
      exact ⟨M', hM', h1.trans ((tail0F hsw i hi st h hm M1 hM1).trans h3)⟩

/-- **The recursion computes midpoint reachability** [AB09, §4.2.1, proof of
Theorem 4.14]: for every level `i ≤ w`, from `cl` on a register file meeting the invariant at
level `i`, the machine reaches `rt b` with `b` the truth value of `Reach (2 ^ w) R i U V`,
changing only `M` (`CallOK`).

**Proof sketch.** Induction on `i`. Level `0` is `base_spec`. At level `i + 1`, `cl` clears
`M` and enters the midpoint loop (`loop_spec`, using the induction hypothesis for the two
descents); the loop's answer from `M = 0` is `Reach (2 ^ w) R (i + 1) U V` by definition. -/
theorem call_spec (hsw : s ≤ w) : ∀ i, i ≤ w → CallOK E orc x s w i := by
  intro i
  induction i with
  | zero =>
    intro _ st h
    exact ⟨st.M, h.hM, base_spec hsw st h⟩
  | succ i ih =>
    intro hi st h
    have IH := ih (by omega)
    have hbd := h.bd hsw hi
    obtain ⟨M', hM', hl⟩ := loop_spec hsw i hi IH (2 ^ w) _ (h.setM (M' := 0) (Nat.zero_le _))
      (by show 0 + 2 ^ w = 2 ^ w; omega)
    refine ⟨M', hM', ?_⟩
    refine step_of hbd ?_
    regs [astep, A, if_neg (show st.I ≠ 0 by rw [h.hI]; omega)]
    refine step_of hbd ?_
    regs [astep, A]
    dsimp only at hl
    have e : (∃ m, 0 ≤ m ∧ m < 2 ^ w ∧ Reach (2 ^ w) (Rel orc x s) i st.U m ∧
        Reach (2 ^ w) (Rel orc x s) i m st.V) ↔ Reach (2 ^ w) (Rel orc x s) (i + 1) st.U st.V :=
      ⟨fun ⟨m, _, h1, h2⟩ => ⟨m, h1, h2⟩, fun ⟨m, h1, h2⟩ => ⟨m, Nat.zero_le _, h1, h2⟩⟩
    rw [decide_eq_decide.mpr e] at hl
    exact hl

end SavitchARM

end Complexity.LogProg
