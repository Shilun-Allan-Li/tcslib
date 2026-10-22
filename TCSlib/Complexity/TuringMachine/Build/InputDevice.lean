/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: input devices (host H5)

An **input device** presents a *virtual* input `y` at a virtual head position `i` inside a host
configuration over a *physical* input `z`, and supplies the two operations a simulated machine
needs: read the virtual cell (`Turing.inputCell y i`: blank at `0` and past the end, the
input-tape convention of `Turing.Cfg.inputSymbol`), and move the virtual head by the clamped
move `Turing.moveInputPos`. It is host H5 of the registry (`machine-library-design.md` §14).
Two devices are stated here.
* **Native** (`Turing.NativeAt`): `z = y`, and the physical head is the virtual one. Nothing is
  stored, and a host step is a source step (literal lockstep). It is the device of H2's step
  block and of `U₀` (`TuringMachine/SelfUniversal.lean`).
* **Bounded-prefix ruler** (`Turing.RulerAt`): `z` is a header of length `ℓ > 0` followed by
  `y`, the physical head is at `ℓ + i`, and a work tape holds the unary ruler `true^ℓ`. Since
  `ℓ > 0`, the physical cell `p - ℓ` is blank exactly at the virtual left boundary, so a
  restoring sweep of `ℓ` cells tests it without clamping. Its storage is the ruler's `ℓ + 2`
  cells. It is the device of the addend-free `Complexity.space_universal`, whose header length
  is linear in the budget.

The buffered device is Z1 (`Build/VirtualInput.lean`). The binary-position device of the
registry row is not stated here; no current consumer needs it.

**The ruler host is a block simulation.** `Turing.exists_rulerHostTM` turns any native-input machine
into one on the suffix input: each source step is one host step, followed by a boundary test after a
left move, so `t` source steps take between `t` and `C · (ℓ + 1) · t` host steps. At every host time
the bank, the output and the ruler are those of the source at some source time (the intermediate
frames), the host does not halt before the source does (the exit cut), and the time and space
ledgers are separate clauses. Literal lockstep is the native special case.

**Status.** The definitions, the devices' correctness facts and the restoring boundary test
`Turing.exists_rulerTestTM` are proved; the call rows `Turing.exists_rulerDeviceTM` and the host
`Turing.exists_rulerHostTM` are sorried with their proof sketches.

## Main definitions

* `Turing.inputCell` — the virtual input cell.
* `Turing.NativeAt` — the native presentation.
* `Turing.RulerAt` — the bounded-prefix ruler presentation.
* `Turing.rulerHostCfg` — the ruler host's layout.

## Main results

* `Turing.Cfg.inputSymbol_eq_inputCell`, `Turing.NativeAt.inputSymbol_eq`,
  `Turing.NativeAt.move`, `Turing.nativeAt_init` — the native device (proved).
* `Turing.inputCell_sub_eq_none_iff`, `Turing.inputCell_of_drop` — the ruler device's
  correctness facts, the empty payload included (proved).
* `Turing.pairEncode_pairEncode_length`, `Turing.pairEncode_pairEncode_drop` — the header of
  `Complexity.space_universal`'s input (proved).
* `Turing.exists_rulerTestTM` — the restoring boundary test (proved).
* `Turing.exists_rulerDeviceTM`, `Turing.exists_rulerHostTM` — the call rows and the host
  (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape, with blanks at both ends;
  Exercise 4.1: the space-bounded universal machine.)
-/

namespace Turing

/-! ### The interface and the native device -/

/-- **The cell of a virtual input at position `i`** (the input-tape convention of
`Turing.Cfg.inputSymbol`): blank at `0` and beyond the word, the `i`-th symbol otherwise.
[AB09, §1.2: the input tape, with blanks at both ends] -/
def inputCell {Γ : Type*} (y : List Γ) (i : ℕ) : Option Γ :=
  if i = 0 then none else y[i - 1]?

/-- The native input symbol is the input cell at the head.

**Proof sketch.** Compare the three cases of `Turing.Cfg.inputSymbol`: position `0`, the right
blank `|y| + 1` (where the lookup is out of range), and the interior
(`Turing.inputSymbolInner`). -/
theorem Cfg.inputSymbol_eq_inputCell {k : ℕ} {Γ S : Type*} {y : List Γ}
    (c : Cfg k Γ S y) : c.inputSymbol = inputCell y c.inputPos.val := by
  have hlt := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have hz : c.inputPos = 0 := Fin.ext h0
    simp [Cfg.inputSymbol, inputCell, hz]
  · by_cases hr : c.inputPos.val = y.length + 1
    · have hz : c.inputPos ≠ 0 := fun h => h0 (by rw [h]; rfl)
      simp only [Cfg.inputSymbol, inputCell, dif_neg hz, dif_pos hr, if_neg h0]
      rw [List.getElem?_eq_none (by omega)]
    · have hin := inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) (by omega)
      rw [hin]
      simp only [inputCell, if_neg h0]
      rw [List.getElem?_eq_getElem (by omega)]

/-- **H5, the native device**: a host configuration presents its own input `y` at virtual
position `i` when its physical input head is at `i`. Reading is the native read, and moving is
the native clamped move; there is nothing to store. This is the device of H2's step block
(its seam relation's input clause) and of `U₀`, whose virtual input is all of its input.
[AB09, §1.2] -/
def NativeAt {K : ℕ} {Γ S : Type*} {y : List Γ} (d : Cfg K Γ S y) (i : Fin (y.length + 2)) :
    Prop :=
  d.inputPos = i

/-- The native device reads the virtual input cell.

**Proof sketch.** `Turing.Cfg.inputSymbol_eq_inputCell` at the head. -/
theorem NativeAt.inputSymbol_eq {K : ℕ} {Γ S : Type*} {y : List Γ} {d : Cfg K Γ S y}
    {i : Fin (y.length + 2)} (h : NativeAt d i) : d.inputSymbol = inputCell y i.val := by
  rw [Cfg.inputSymbol_eq_inputCell, h]

/-- The native device moves the virtual head by the clamped move. -/
theorem NativeAt.move {K : ℕ} {Γ S : Type*} {y : List Γ} {d : Cfg K Γ S y}
    {i : Fin (y.length + 2)} (h : NativeAt d i) (m : SignType) :
    NativeAt { d with inputPos := moveInputPos d.inputPos m } (moveInputPos i m) := by
  unfold NativeAt at h ⊢
  rw [h]

/-- The initial configuration presents its input natively at position `1`, the position at
which `U₀`'s startup must leave its input head (the RD-3 gate's check 2). -/
theorem nativeAt_init {K : ℕ} {Γ S : Type*} (q₀ : S) (y : List Γ) :
    NativeAt (Cfg.init q₀ y : Cfg K Γ S y) 1 := rfl

/-! ### The bounded-prefix ruler device -/

/-- **The boundary test reads a blank exactly at the virtual left boundary.** If the header
length `ℓ` is positive and the physical head is at `p` with `ℓ ≤ p ≤ |z| + 1`, then the
physical input cell `p - ℓ` is blank exactly when `p = ℓ`. This holds for every `z`, so for an
empty payload as well (the RD-3 gate's suggested sanity obligation for the bounded-prefix
device).

**Proof sketch.** At `p = ℓ` the cell is position `0`. Otherwise `1 ≤ p - ℓ ≤ |z|`, since
`ℓ ≥ 1`, and the cell holds an input symbol. -/
theorem inputCell_sub_eq_none_iff {z : List Bool} {ℓ p : ℕ} (hℓ : 0 < ℓ) (hp : ℓ ≤ p)
    (hpz : p ≤ z.length + 1) : inputCell z (p - ℓ) = none ↔ p = ℓ := by
  unfold inputCell
  by_cases h : p - ℓ = 0
  · simp only [if_pos h, true_iff]
    omega
  · rw [if_neg h, List.getElem?_eq_getElem (by omega)]
    simp only [reduceCtorEq, false_iff]
    omega

/-- **Away from the boundary the virtual cell is the physical one.** If `y` is `z` without
its first `ℓ` symbols, the virtual cell `i ≠ 0` of `y` is the physical cell `ℓ + i` of `z`,
the right blank included.

**Proof sketch.** Both are the lookup of `z` at `ℓ + i - 1` (`List.getElem?_drop`). -/
theorem inputCell_of_drop {z y : List Bool} {ℓ : ℕ} (h : z.drop ℓ = y) {i : ℕ}
    (hi : i ≠ 0) : inputCell y i = inputCell z (ℓ + i) := by
  subst h
  unfold inputCell
  rw [if_neg hi, if_neg (by omega), List.getElem?_drop]
  congr 1
  omega

/-- **H5, the bounded-prefix ruler device** (the RD-3 gate's row 1): a host configuration `d`
over the physical input `z` presents the virtual input `y` at virtual position `i` with header
length `ℓ` and ruler tape `r` when `z` is a header of length `ℓ > 0` followed by `y`, the
physical head is at `ℓ + i`, and tape `r` holds, from its head, the delimited unary ruler
`true^ℓ`. Since `ℓ > 0`, the physical cell `i` is blank exactly when `i = 0`, so a sweep of
`ℓ` cells left, a read and a sweep back test the virtual left boundary without clamping. The
ruler's cells are the device's whole storage: `ℓ + 2` visited cells, however far the virtual
head travels. [AB09, §1.2; Exercise 4.1] -/
def RulerAt {K : ℕ} {S : Type*} {y z : List Bool} (ℓ : ℕ) (r : Fin K) (d : Cfg K Bool S z)
    (i : Fin (y.length + 2)) : Prop :=
  0 < ℓ ∧ ℓ ≤ z.length ∧ z.drop ℓ = y ∧ d.inputPos.val = ℓ + i.val ∧
    ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape (List.replicate ℓ true) p

/-- **The header length of `Complexity.space_universal`'s input.** The input
`⟨bits s, ⟨α, x⟩⟩ = pairEncode (bits s) (pairEncode α x)` is a header of length
`2|bits s| + 2|α| + 4` followed by `x`.

**Proof sketch.** Each pairing doubles its first word and adds two separator cells
(`Turing.universal_pair_length`). -/
theorem pairEncode_pairEncode_length (u α x : List Bool) :
    (pairEncode u (pairEncode α x)).length = (2 * u.length + 2 * α.length + 4) + x.length := by
  rw [universal_pair_length, universal_pair_length]
  omega

/-- **The payload after the header.** Dropping the header of length `2|u| + 2|α| + 4` from
`pairEncode u (pairEncode α x)` leaves `x`: the ruler device's `z.drop ℓ = y`.

**Proof sketch.** Drop the two pairings' prefixes one after the other. -/
theorem pairEncode_pairEncode_drop (u α x : List Bool) :
    (pairEncode u (pairEncode α x)).drop (2 * u.length + 2 * α.length + 4) = x := by
  have hd (v z : List Bool) : (pairEncode v z).drop (2 * v.length + 2) = z := by
    have hl : ((v.flatMap fun b => [b, b]) ++ [false, true]).length = 2 * v.length + 2 := by
      have h := universal_pair_length v []
      simpa [pairEncode] using h
    rw [show pairEncode v z = ((v.flatMap fun b => [b, b]) ++ [false, true]) ++ z from rfl]
    exact List.drop_left' hl
  rw [show 2 * u.length + 2 * α.length + 4 = (2 * u.length + 2) + (2 * α.length + 2) by ring,
    ← List.drop_drop, hd, hd]

/-- The forward state, followed by return and verdict states carrying one Boolean. -/
private abbrev rd_State := Unit ⊕ Bool × Bool

/-- The ruler test is a leaf: scan jointly left/right, read once, and return jointly.
No catalog row moves the input head together with a work head. -/
private def rd_test : MultiTapeTM 1 Bool rd_State where
  q₀ := .inl ()
  tr q v w := match q with
    | .inl _ => if w 0 = some true then tapeAction 0 (-1) none 1 (.inl ())
        else tapeAction 0 0 none (-1) (.inr (v.isNone, false))
    | .inr (b, false) => if w 0 = some true then tapeAction 0 1 none (-1) (.inr (b, false))
        else tapeAction 0 0 none 1 (.inr (b, true))
    | .inr (b, true) => tapeAction 0 0 none 0 (.inr (b, true))

/-- A point of the restoring trace, with distance from the original input head. -/
private def rd_cfg {z : List Bool} (d : Cfg 1 Bool rd_State z) (q : rd_State)
    (n : ℕ) (e : ℤ) : Cfg 1 Bool rd_State z :=
  { d with
    state := some q
    inputPos := ⟨d.inputPos.val - n, by have := d.inputPos.isLt; omega⟩
    workTapePos := fun i => d.workTapePos i + e }

/-- The verdict says precisely whether the physical head equals the header length. -/
private def rd_verdict {z : List Bool} (d : Cfg 1 Bool rd_State z) (ℓ : ℕ) : Bool :=
  decide (d.inputPos.val = ℓ)

/-- The whole finite trace has a forward leg, a return leg and one restored endpoint. -/
private def rd_trace {z : List Bool} (d : Cfg 1 Bool rd_State z) (ℓ u : ℕ) :=
  if u ≤ ℓ then rd_cfg d (.inl ()) u u
  else if u ≤ 2 * ℓ + 1 then
    let n := 2 * ℓ + 1 - u
    rd_cfg d (.inr (rd_verdict d ℓ, false)) n ((n : ℤ) - 1)
  else rd_cfg d (.inr (rd_verdict d ℓ, true)) 0 0

/-- The ruler gives a true cell at each interior natural offset. -/
private theorem rd_read_nat {z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool rd_State z)
    (hr : ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p)
    (n : ℕ) (hn : n < ℓ) : d.workTapes 0 (d.workTapePos 0 + n) = some true := by
  rw [hr n (by omega) (by omega), FinTM.bufferTape_nat]
  simp only [List.getElem?_replicate, if_pos hn]

/-- One table row moves between two trace points using `Turing.step_of_tapeAction_move`. -/
private theorem rd_cfg_step {z : List Bool} (d : Cfg 1 Bool rd_State z)
    (q q' : rd_State) (n n' : ℕ) (e e' : ℤ) (a b : SignType)
    (ht : rd_test.tr q (rd_cfg d q n e).inputSymbol
      (rd_cfg d q n e).workTapeSymbols = tapeAction 0 a none b q')
    (hi : moveInputPos (rd_cfg d q n e).inputPos a = (rd_cfg d q' n' e').inputPos)
    (he : e + (b : ℤ) = e') :
    rd_test.step (rd_cfg d q n e) = rd_cfg d q' n' e' := by
  rw [step_of_tapeAction_move rd_test (rd_cfg d q n e) 0 a b rfl ht]
  refine Cfg.ext rfl hi rfl ?_ rfl
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Function.update_self, rd_cfg, add_assoc, he]

/-- Each successive point follows the table, including both delimiter turns.

**Proof sketch.** Interior ruler cells move both heads; the right delimiter records the
semantic boundary test, and the left delimiter restores the ruler head before the verdict. -/
private theorem rd_trace_step {z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool rd_State z)
    (hℓ : 0 < ℓ) (hp : ℓ ≤ d.inputPos.val)
    (hr : ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p)
    (u : ℕ) (hu : u < 2 * ℓ + 2) :
    rd_test.step (rd_trace d ℓ u) = rd_trace d ℓ (u + 1) := by
  by_cases hf : u < ℓ
  · simp only [rd_trace, if_pos (show u ≤ ℓ by omega),
      if_pos (show u + 1 ≤ ℓ by omega)]
    refine rd_cfg_step d _ _ _ _ _ _ (-1) 1 ?_ ?_ (by simp only [SignType.coe_one]; omega)
    · simp only [rd_test, Cfg.workTapeSymbols_eq, rd_cfg, rd_read_nat ℓ d hr u hf,
        if_true]
    · rw [← SignType.neg_eq_neg_one]
      rw [moveInputPos_neg_of_ne_left (rd_cfg d (.inl ()) u u).inputPos (by
        intro h; have hh := congrArg Fin.val h; simp only [rd_cfg, Fin.val_zero] at hh
        omega)]
      apply Fin.ext
      simp only [rd_cfg]
      omega
  · by_cases ht : u = ℓ
    · subst u
      have hb : (inputCell z (d.inputPos.val - ℓ)).isNone = rd_verdict d ℓ := by
        rw [Bool.eq_iff_iff]
        simp only [Option.isNone_iff_eq_none, rd_verdict, decide_eq_true_eq]
        exact inputCell_sub_eq_none_iff hℓ hp (by have := d.inputPos.isLt; omega)
      have hend : d.workTapes 0 (d.workTapePos 0 + ℓ) = none := by
        rw [hr ℓ (by omega) (by omega), FinTM.bufferTape_nat]
        simp only [List.getElem?_replicate, lt_self_iff_false, if_false]
      simp only [rd_trace, if_pos (show ℓ ≤ ℓ from le_rfl),
        if_neg (show ¬ℓ + 1 ≤ ℓ by omega), if_pos (show ℓ + 1 ≤ 2 * ℓ + 1 by omega)]
      have hn : 2 * ℓ + 1 - (ℓ + 1) = ℓ := by omega
      rw [hn]
      refine rd_cfg_step d _ _ _ _ _ _ 0 (-1) ?_ ?_ (by
        simp only [SignType.coe_neg_one]; omega)
      · simp only [rd_test, Cfg.workTapeSymbols_eq, rd_cfg, hend, reduceCtorEq, if_false,
          Cfg.inputSymbol_eq_inputCell, hb]
      · exact moveInputPos_zero _
    · have hf' : ¬u ≤ ℓ := by omega
      have hf'' : ¬u + 1 ≤ ℓ := by omega
      have hrange : u ≤ 2 * ℓ + 1 := by omega
      by_cases he : u = 2 * ℓ + 1
      · subst u
        have hend : d.workTapes 0 (d.workTapePos 0 + (-1)) = none := by
          rw [hr (-1) (by omega) (by omega), FinTM.bufferTape_left]
        simp only [rd_trace, if_neg hf', if_neg hf'', if_pos (le_refl (2 * ℓ + 1)),
          if_neg (show ¬2 * ℓ + 1 + 1 ≤ 2 * ℓ + 1 by omega), Nat.sub_self,
          Nat.cast_zero, zero_sub]
        refine rd_cfg_step d _ _ _ _ _ _ 0 1 ?_ ?_ (by simp)
        · simp only [rd_test, Cfg.workTapeSymbols_eq, rd_cfg, hend, reduceCtorEq, if_false]
        · exact moveInputPos_zero _
      · have hnext : u + 1 ≤ 2 * ℓ + 1 := by omega
        let n := 2 * ℓ + 1 - u
        have hn : 0 < n ∧ n ≤ ℓ := by dsimp [n]; omega
        have hnextn : 2 * ℓ + 1 - (u + 1) = n - 1 := by dsimp [n]; omega
        have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
        have hread : d.workTapes 0 (d.workTapePos 0 + ((n : ℤ) - 1)) = some true := by
          rw [← hcast]
          exact rd_read_nat ℓ d hr (n - 1) (by omega)
        simp only [rd_trace, if_neg hf', if_neg hf'', if_pos hrange, if_pos hnext]
        change rd_test.step (rd_cfg d (.inr (rd_verdict d ℓ, false)) n ((n : ℤ) - 1)) = _
        rw [hnextn]
        refine rd_cfg_step d _ _ _ _ _ _ 1 (-1) ?_ ?_ (by
          simp only [SignType.coe_neg_one]; omega)
        · simp only [rd_test, Cfg.workTapeSymbols_eq, rd_cfg, hread, if_true]
        · rw [← SignType.pos_eq_one]
          rw [moveInputPos_pos_of_ne_right
            (rd_cfg d (.inr (rd_verdict d ℓ, false)) n ((n : ℤ) - 1)).inputPos (by
            change d.inputPos.val - n ≠ z.length + 1
            have := d.inputPos.isLt; omega)]
          apply Fin.ext
          simp only [rd_cfg]
          omega

/-- The single induction that identifies every point of the finite restoring sweep. -/
private theorem rd_run {z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool rd_State z)
    (hd : d.state = some (.inl ())) (hℓ : 0 < ℓ) (hp : ℓ ≤ d.inputPos.val)
    (hr : ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p)
    (u : ℕ) (hu : u ≤ 2 * ℓ + 2) : rd_test.runFrom d u = rd_trace d ℓ u := by
  induction u with
  | zero =>
    rw [MultiTapeTM.runFrom_zero]
    simp only [rd_trace, Nat.zero_le, if_true, rd_cfg, Nat.sub_zero, Nat.cast_zero, add_zero]
    exact Cfg.ext hd rfl rfl rfl rfl
  | succ u ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact rd_trace_step ℓ d hℓ hp hr u (by omega)

/-- **The restoring suffix-boundary test** (the ruler device's core). There is a one-tape binary
module with an entry and two distinct verdicts as follows. Start it at its entry with the
delimited ruler `true^ℓ`, `ℓ > 0`, at its head and the physical input head at a position `p ≥ ℓ`.
It reaches `yes` if `p = ℓ` and `no` otherwise, within `C · (ℓ + 1)` steps and no verdict
earlier, with nothing else changed: the input head is back at `p` and the ruler head at its
start, having stayed within `ℓ + 1` cells.
The input itself is arbitrary, so an empty payload is included. [AB09, §1.2]

**Proof sketch.** Move the input head left and the ruler head right in lockstep until the ruler
head reads the blank after the ruler: `ℓ` moves, none clamped since `p ≥ ℓ`. Read the input cell
at `p - ℓ`: it is blank exactly when `p - ℓ = 0`, since `p - ℓ ≤ |z| + 1 - ℓ ≤ |z|`
(`Turing.inputCell_sub_eq_none_iff`). Move both heads back `ℓ` cells (the ruler head stops at
the blank before the ruler, then steps right). A finite control carries the verdict.

**Implementation.** The test is a hand-built controller that moves the input head and the
ruler head in the same step (a `Turing.tapeAction`); no catalog row does that. One
forward-and-return trajectory, identified by a single induction, takes exactly `2ℓ + 2` steps, so
`C = 2`. The turn reads the boundary through `Turing.inputCell_sub_eq_none_iff`; the return leg
changes no tape and no output and restores both heads. -/
theorem exists_rulerTestTM :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 1 Bool P)
      (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool P z), d.state = some entry → 0 < ℓ →
        ℓ ≤ d.inputPos.val →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p) →
        ∃ t ≤ C * (ℓ + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, |(R.runFrom d u).workTapePos 0 - d.workTapePos 0| ≤ ((ℓ + 1 : ℕ) : ℤ)) ∧
          R.runFrom d t = { d with state := some (if d.inputPos.val = ℓ then yes else no) } := by
  refine ⟨rd_State, inferInstance, inferInstance, rd_test, .inl (), .inr (true, true),
    .inr (false, true), 2, by decide, ?_⟩
  intro z ℓ d hd hℓ hp hr
  refine ⟨2 * ℓ + 2, by omega, ?_, ?_, ?_⟩
  · intro u hu
    rw [rd_run ℓ d hd hℓ hp hr u (by omega)]
    by_cases hf : u ≤ ℓ
    · simp only [rd_trace, if_pos hf, rd_cfg]
      constructor <;> intro h <;> cases h
    · have hu' : u ≤ 2 * ℓ + 1 := by omega
      simp only [rd_trace, if_neg hf, if_pos hu', rd_cfg]
      constructor <;> intro h
      all_goals exact Bool.false_ne_true (congrArg Prod.snd (Sum.inr.inj (Option.some.inj h)))
  · intro u hu
    rw [rd_run ℓ d hd hℓ hp hr u hu]
    by_cases hf : u ≤ ℓ
    · simp only [rd_trace, if_pos hf, rd_cfg, add_sub_cancel_left, abs_le]
      constructor <;> omega
    · by_cases hb : u ≤ 2 * ℓ + 1
      · simp only [rd_trace, if_neg hf, if_pos hb, rd_cfg, add_sub_cancel_left, abs_le]
        constructor <;> omega
      · simp only [rd_trace, if_neg hf, if_neg hb, rd_cfg, add_zero, sub_self, abs_zero]
        omega
  · rw [rd_run ℓ d hd hℓ hp hr (2 * ℓ + 2) (le_refl _)]
    simp only [rd_trace, if_neg (show ¬2 * ℓ + 2 ≤ ℓ by omega),
      if_neg (show ¬2 * ℓ + 2 ≤ 2 * ℓ + 1 by omega), rd_cfg, Nat.sub_zero, add_zero]
    refine Cfg.ext ?_ rfl rfl rfl rfl
    by_cases h : d.inputPos.val = ℓ
    · simp only [rd_verdict, h, decide_true, if_true]
    · simp only [rd_verdict, h, decide_false, if_false]

/-- The concrete test's frames and its two-sided head envelope, projected from `rd_run`. -/
private theorem rd_test_window {z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool rd_State z)
    (hd : d.state = some (.inl ())) (hℓ : 0 < ℓ) (hp : ℓ ≤ d.inputPos.val)
    (hr : ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p)
    (u : ℕ) (hu : u ≤ 2 * ℓ + 2) :
    (rd_test.runFrom d u).workTapes = d.workTapes ∧
    (rd_test.runFrom d u).output = d.output ∧
    d.workTapePos 0 - 1 ≤ (rd_test.runFrom d u).workTapePos 0 ∧
    (rd_test.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + ℓ ∧
    (rd_test.runFrom d u).state ≠ none ∧
    (u < 2 * ℓ + 2 → ∀ b, (rd_test.runFrom d u).state ≠ some (.inr (b, true))) := by
  rw [rd_run ℓ d hd hℓ hp hr u hu]
  unfold rd_trace
  split_ifs with hf hb
  · simp only [rd_cfg, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact ⟨by omega, by omega, by simp⟩
  · simp only [rd_cfg, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    refine ⟨by omega, by omega, ?_⟩
    intro _ b h
    exact Bool.false_ne_true (congrArg Prod.snd (Sum.inr.inj (Option.some.inj h)))
  · simp only [rd_cfg, add_zero, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact ⟨by omega, by omega, fun h => False.elim (by omega)⟩

/-- The restored endpoint of the same test; no second trajectory argument is needed. -/
private theorem rd_test_return {z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool rd_State z)
    (hd : d.state = some (.inl ())) (hℓ : 0 < ℓ) (hp : ℓ ≤ d.inputPos.val)
    (hr : ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p) :
    rd_test.runFrom d (2 * ℓ + 2) =
      { d with state := some (.inr (rd_verdict d ℓ, true)) } := by
  rw [rd_run ℓ d hd hℓ hp hr _ le_rfl]
  simp only [rd_trace, if_neg (show ¬2 * ℓ + 2 ≤ ℓ by omega),
    if_neg (show ¬2 * ℓ + 2 ≤ 2 * ℓ + 1 by omega), rd_cfg, Nat.sub_zero, add_zero]

/-- Read answers occupy three pairs; the unused fourth pair is the move exit. -/
private def rd_answer : Option Bool → Bool × Bool
  | none => (false, false)
  | some b => (true, b)

/-- Only a left move at the virtual boundary is suppressed. -/
private def rd_direction (m : SignType) (b : Bool) : SignType :=
  if b = true ∧ m = -1 then 0 else m

/-- The parameter selects a read or a move, sharing the same test and dispatch proof. -/
private def rd_leafMove (op : Option SignType) (b : Bool) : SignType :=
  op.elim 0 (fun m => rd_direction m b)

private def rd_leafAnswer (op : Option SignType) (b : Bool) (inp : Option Bool) : Bool × Bool :=
  op.elim (rd_answer (if b then none else inp)) (fun _ => (false, true))

/-- The leaf uses the public input-only action, including a stationary read. -/
private def rd_callLeaf (op : Option SignType) (b : Bool) : MultiTapeTM 1 Bool rd_State where
  q₀ := .inl ()
  tr := fun _ inp _ =>
    inputMoveAction (rd_leafMove op b) (.inr (rd_leafAnswer op b inp))

private abbrev rd_Phase := Option SignType ⊕ (Option SignType × Bool ⊕ Unit)
private abbrev rd_CallState := Σ _ : rd_Phase, rd_State

private def rd_family : rd_Phase → MultiTapeTM 1 Bool rd_State
  | .inr (.inl (op, b)) => rd_callLeaf op b
  | _ => rd_test

private def rd_redirect : (i : rd_Phase) → rd_State → Option rd_CallState
  | .inl op, .inr (b, true) => some ⟨.inr (.inl (op, b)), .inl ()⟩
  | .inr (.inl _), .inr a => some ⟨.inr (.inr ()), .inr a⟩
  | _, _ => none

private def rd_callTM : MultiTapeTM 1 Bool rd_CallState :=
  phaseHostTM rd_family ⟨.inl none, .inl ()⟩ rd_redirect

/-- Both call rows are two applications of the public phase lemma. -/
private theorem rd_call_run {z : List Bool} (op : Option SignType) (ℓ : ℕ)
    (d : Cfg 1 Bool rd_CallState z) (hd : d.state = some ⟨.inl op, .inl ()⟩)
    (hℓ : 0 < ℓ) (hp : ℓ ≤ d.inputPos.val)
    (hr : ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (List.replicate ℓ true) p) :
    let b := decide (d.inputPos.val = ℓ)
    let a := rd_leafAnswer op b d.inputSymbol
    rd_callTM.runFrom d (2 * ℓ + 5) =
      { d with
        state := some ⟨.inr (.inr ()), .inr a⟩
        inputPos := moveInputPos d.inputPos (rd_leafMove op b) } ∧
    (∀ u < 2 * ℓ + 5, ∀ q, (rd_callTM.runFrom d u).state ≠
      some ⟨.inr (.inr ()), q⟩) ∧
    (∀ u ≤ 2 * ℓ + 5,
      |(rd_callTM.runFrom d u).workTapePos 0 - d.workTapePos 0| ≤ ((ℓ + 1 : ℕ) : ℤ)) := by
  let c : Cfg 1 Bool rd_State z :=
    ⟨some (.inl ()), d.inputPos, d.workTapes, d.workTapePos, d.output⟩
  let b := rd_verdict c ℓ
  let a := rd_leafAnswer op b c.inputSymbol
  let i : rd_Phase := .inr (.inl (op, b))
  let e : Cfg 1 Bool rd_State z := { c with state := some (.inr (b, true)) }
  let f : Cfg 1 Bool rd_State z := { c with
    state := some (.inr a)
    inputPos := moveInputPos c.inputPos (rd_leafMove op b) }
  have hc : c.state = some (.inl ()) := rfl
  have hstart : c.mapState (Sigma.mk (.inl op)) = d := by
    apply Cfg.ext
    · simp only [Cfg.mapState_state, hc, Option.map_some, hd]
    · exact Cfg.mapState_inputPos _ _
    · funext j p; rw [Cfg.mapState_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos]
    · exact Cfg.mapState_output _ _
  have test := phaseHostTM_run rd_family ⟨.inl none, .inl ()⟩ rd_redirect
    (.inl op) c e (2 * ℓ + 2) (rd_test_return ℓ c hc hℓ hp hr)
    (.inr (b, true)) rfl ⟨i, .inl ()⟩ rfl (by
      intro u hu q hq
      have hcut := (rd_test_window ℓ c hc hℓ hp hr u (by omega)).2.2.2.2.2 hu
      cases q with
      | inl q => rfl
      | inr q =>
        rcases q with ⟨v, flag⟩
        cases flag
        · rfl
        · exact False.elim (hcut v hq))
  have hdispatch : e.mapState (fun _ => (⟨i, .inl ()⟩ : rd_CallState)) =
      c.mapState (Sigma.mk i) := by
    apply Cfg.ext
    · simp only [Cfg.mapState_state, e, hc, Option.map_some]
    · simp only [Cfg.mapState_inputPos, e]
    · funext j p; simp only [Cfg.mapState_workTapes, e]
    · funext j; simp only [Cfg.mapState_workTapePos, e]
    · simp only [Cfg.mapState_output, e]
  have hleaf : (rd_family i).runFrom c 1 = f := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    exact step_of_inputMoveAction (rd_callLeaf op b) c (rd_leafMove op b) hc rfl
  have leaf := phaseHostTM_run rd_family ⟨.inl none, .inl ()⟩ rd_redirect i c f 1
    hleaf (.inr a) rfl ⟨.inr (.inr ()), .inr a⟩ rfl (by
      intro u hu q hq
      have hu0 : u = 0 := by omega
      rw [hu0, MultiTapeTM.runFrom_zero, hc] at hq
      have hq' := Option.some.inj hq
      subst q
      rfl)
  have hjoin : rd_callTM.runFrom d (2 * ℓ + 3) = c.mapState (Sigma.mk i) := by
    rw [← hstart]
    exact test.2.trans hdispatch
  have hlast : rd_callTM.runFrom d (2 * ℓ + 5) =
      f.mapState (fun _ => (⟨.inr (.inr ()), .inr a⟩ : rd_CallState)) := by
    rw [show 2 * ℓ + 5 = (2 * ℓ + 3) + 2 by omega, MultiTapeTM.runFrom_add, hjoin]
    exact leaf.2
  have hinp : c.inputSymbol = d.inputSymbol := by
    rw [Cfg.inputSymbol_eq_inputCell, Cfg.inputSymbol_eq_inputCell]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlast]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, f, Option.map_some, a, hinp, b, rd_verdict, c]
    · exact Cfg.mapState_inputPos _ _
    · funext j p; rw [Cfg.mapState_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos]
    · exact Cfg.mapState_output _ _
  · intro u hu q hq
    by_cases ht : u ≤ 2 * ℓ + 2
    · rw [← hstart, test.1 u ht, Cfg.mapState_state] at hq
      obtain ⟨s, _, hs⟩ := Option.map_eq_some_iff.mp hq
      have := congrArg Sigma.fst hs
      cases this
    · have hv : u = (2 * ℓ + 3) + (u - (2 * ℓ + 3)) := by omega
      rw [hv, MultiTapeTM.runFrom_add, hjoin,
        leaf.1 (u - (2 * ℓ + 3)) (by omega), Cfg.mapState_state] at hq
      obtain ⟨s, _, hs⟩ := Option.map_eq_some_iff.mp hq
      have := congrArg Sigma.fst hs
      cases this
  · intro u hu
    by_cases ht : u ≤ 2 * ℓ + 2
    · rw [← hstart, test.1 u ht, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos]
      have hw := rd_test_window ℓ c hc hℓ hp hr u ht
      rw [abs_le]
      constructor <;> have := hw.2.2 <;> push_cast <;> omega
    · by_cases he : u = 2 * ℓ + 5
      · rw [he, hlast, Cfg.mapState_workTapePos]
        simp only [f, c, sub_self, abs_zero]
        positivity
      · have hv : u = (2 * ℓ + 3) + (u - (2 * ℓ + 3)) := by omega
        rw [hv, MultiTapeTM.runFrom_add, hjoin,
          leaf.1 (u - (2 * ℓ + 3)) (by omega), Cfg.mapState_workTapePos]
        have hv' : u - (2 * ℓ + 3) = 0 ∨ u - (2 * ℓ + 3) = 1 := by omega
        rcases hv' with hv' | hv'
        · rw [hv', MultiTapeTM.runFrom_zero]
          simp only [c, sub_self, abs_zero]; positivity
        · rw [hv', hleaf]
          simp only [f, c, sub_self, abs_zero]; positivity

/-- Translation of the clamped input move, including both blanks of an empty payload. -/
private theorem rd_shift_move {y z : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + y.length) (p : Fin (z.length + 2)) (i : Fin (y.length + 2))
    (hp : p.val = ℓ + i.val) (b : Bool) (hb : b = true ↔ i.val = 0) (m : SignType) :
    (moveInputPos p (rd_direction m b)).val = ℓ + (moveInputPos i m).val := by
  cases m with
  | zero => simpa only [rd_direction, SignType.zero_eq_zero, reduceCtorEq,
      and_false, if_false, moveInputPos_zero] using hp
  | neg =>
    by_cases hi : i.val = 0
    · have hbt : b = true := hb.mpr hi
      have hm : rd_direction .neg b = 0 := by simp [rd_direction, hbt]
      rw [hm, moveInputPos_zero, FinTM.moveInputPos_neg_val]
      omega
    · have hbf : b ≠ true := fun h => hi (hb.mp h)
      have hm : rd_direction .neg b = .neg := by simp [rd_direction, hbf]
      rw [hm, FinTM.moveInputPos_neg_val, FinTM.moveInputPos_neg_val]
      omega
  | pos =>
    have hm : rd_direction .pos b = .pos := by simp [rd_direction]
    rw [hm]
    by_cases hi : i.val = y.length + 1
    · have he : i = ⟨y.length + 1, by omega⟩ := Fin.ext hi
      have hp' : p = ⟨z.length + 1, by omega⟩ := by
        apply Fin.ext; change p.val = z.length + 1; omega
      rw [he, hp', SignType.pos_eq_one, moveInputPos_rightBoundary,
        moveInputPos_rightBoundary]
      simp only; omega
    · rw [moveInputPos_pos_of_ne_right i hi,
        moveInputPos_pos_of_ne_right p (by omega)]
      simp only; omega

/-- The tagged physical read is the virtual read, including its right blank. -/
private theorem rd_tagged_read {S : Type} {y z : List Bool} (ℓ : ℕ)
    (hdrop : z.drop ℓ = y) (d : Cfg 1 Bool S z) (i : Fin (y.length + 2))
    (hp : d.inputPos.val = ℓ + i.val) (b : Bool) (hb : b = true ↔ i.val = 0) :
    (if b then none else d.inputSymbol) = inputCell y i.val := by
  cases b with
  | false =>
    have hi : i.val ≠ 0 := fun h => Bool.false_ne_true (hb.mpr h)
    change d.inputSymbol = inputCell y i.val
    rw [Cfg.inputSymbol_eq_inputCell, hp, ← inputCell_of_drop hdrop hi]
  | true =>
    have hi := hb.mp rfl
    simp only [if_true, hi, inputCell, if_true]

/-- **H5, the ruler device's call rows** ("read the virtual input cell", "move the virtual input
head"). There is a one-tape binary module with a read entry, three read verdicts
`readExit v`, a move entry per direction and a move exit, as follows, for every presentation
`Turing.RulerAt ℓ 0 d i` of a virtual input `y` at `i`.
* **Read**: from the read entry it reaches `readExit (inputCell y i)` within `C · (ℓ + 1)`
  steps, no read verdict earlier, with nothing else changed.
* **Move** by `m`: from `moveEntry m` it reaches the move exit within `C · (ℓ + 1)` steps, not
  earlier, with the physical head at `ℓ + (moveInputPos i m)` and every tape, every head and
  the output unchanged; so the result presents `y` at the clamped position `moveInputPos i m`.

In both, the ruler head stays within `ℓ + 1` cells of its start, so the device's work space is
`ℓ + 2` cells. These rows are the interface for a device-generic step block; the ruler host
below uses the boundary test directly. [AB09, §1.2]

**Proof sketch.** Both rows begin with the boundary test of `Turing.exists_rulerTestTM`. Read:
on `yes` answer blank; on `no` answer the native symbol under the head, which is
`y[i - 1]` or the right blank (`Turing.inputCell_of_drop`). Move: a right move is the native
clamped move (at `i = |y| + 1` the physical head is at `|z| + 1` and clamps exactly as
`moveInputPos` does); a stationary move does nothing; a left move is suppressed on `yes` and is
the native left move on `no`. Rows are joined by R2 seams; the dispatch steps add a constant.

**Implementation status.** Both call rows are proved by the same two-phase argument. Each takes
exactly `2ℓ + 5` steps, with `C = 4`, and uses the public input-only action for its leaf.
-/
theorem exists_rulerDeviceTM :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 1 Bool P)
      (readEntry : P) (readExit : Option Bool → P) (moveEntry : SignType → P) (moveExit : P)
      (C : ℕ),
      Function.Injective readExit ∧ (∀ v, readExit v ≠ moveExit) ∧
      ∀ {y z : List Bool} (ℓ : ℕ) (d : Cfg 1 Bool P z) (i : Fin (y.length + 2)),
        RulerAt ℓ 0 d i →
        (d.state = some readEntry →
          ∃ t ≤ C * (ℓ + 1),
            (∀ u < t, ∀ v, (R.runFrom d u).state ≠ some (readExit v)) ∧
            (∀ u ≤ t, |(R.runFrom d u).workTapePos 0 - d.workTapePos 0| ≤ ((ℓ + 1 : ℕ) : ℤ)) ∧
            R.runFrom d t = { d with state := some (readExit (inputCell y i.val)) }) ∧
        (∀ m : SignType, d.state = some (moveEntry m) →
          ∃ t ≤ C * (ℓ + 1),
            (∀ u < t, (R.runFrom d u).state ≠ some moveExit) ∧
            (∀ u ≤ t, |(R.runFrom d u).workTapePos 0 - d.workTapePos 0| ≤ ((ℓ + 1 : ℕ) : ℤ)) ∧
            (R.runFrom d t).state = some moveExit ∧
            (R.runFrom d t).inputPos.val = ℓ + (moveInputPos i m).val ∧
            (R.runFrom d t).workTapes = d.workTapes ∧
            (R.runFrom d t).workTapePos = d.workTapePos ∧
            (R.runFrom d t).output = d.output) := by
  refine ⟨rd_CallState, inferInstance, inferInstance, rd_callTM,
    ⟨.inl none, .inl ()⟩, (fun v => ⟨.inr (.inr ()), .inr (rd_answer v)⟩),
    (fun m => ⟨.inl (some m), .inl ()⟩), ⟨.inr (.inr ()), .inr (false, true)⟩,
    4, ?_, ?_, ?_⟩
  · intro v w h
    cases v <;> cases w <;> simp_all [rd_answer]
  · intro v h
    cases v <;> simp_all [rd_answer]
  · intro y z ℓ d i h
    rcases h with ⟨hℓ, hlen, hdrop, hp, hr⟩
    have hz : z.length = ℓ + y.length := by
      have := congrArg List.length hdrop
      rw [List.length_drop] at this
      omega
    have hb : decide (d.inputPos.val = ℓ) = true ↔ i.val = 0 := by
      rw [decide_eq_true_eq]; omega
    constructor
    · intro hd
      obtain ⟨he, hcut, hspace⟩ := rd_call_run none ℓ d hd hℓ (by omega) hr
      refine ⟨2 * ℓ + 5, by omega, fun u hu v => hcut u hu (.inr (rd_answer v)),
        hspace, ?_⟩
      have hs := rd_tagged_read ℓ hdrop d i hp _ hb
      simpa only [rd_leafMove, rd_leafAnswer, Option.elim_none,
        moveInputPos_zero, hs] using he
    · intro m hd
      obtain ⟨he, hcut, hspace⟩ := rd_call_run (some m) ℓ d hd hℓ (by omega) hr
      refine ⟨2 * ℓ + 5, by omega, fun u hu => hcut u hu (.inr (false, true)),
        hspace, ?_⟩
      rw [he]
      refine ⟨rfl, ?_, rfl, rfl, rfl⟩
      exact rd_shift_move ℓ hz d.inputPos i hp _ hb m

/-- **The ruler host layout**: a configuration `c` of an `m`-tape machine on the virtual input
`y`, viewed over the physical input `z` with a header of length `ℓ`: the control `q`, the
physical input head at `ℓ + c`'s position, `c`'s work tapes and heads first, the ruler tape
`rt` with its head at `rp` last, and `c`'s output. -/
def rulerHostCfg {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + y.length) (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool)
    (rp : ℤ) : Cfg (m + 1) Bool Q z :=
  ⟨q, ⟨ℓ + c.inputPos.val, by have := c.inputPos.isLt; omega⟩, Fin.lastCases rt c.workTapes,
    Fin.lastCases rp c.workTapePos, c.output⟩

/-- **H5, the ruler host**: a positive, finite block simulation of any native-input machine on
a suffix input (the H2-S gate's finding 2). For any binary machine `M` on `m` tapes there is a
host on one more tape (the ruler, last), with a state map `inj` of the source states paired
with a boundary tag, as follows. Present a source configuration `c` on the virtual input `y`
inside `z = header ++ y` (header length `ℓ > 0`) through `Turing.rulerHostCfg`, with the ruler
`true^ℓ` at the ruler head and the tag `b` true exactly at the virtual left boundary. Then for
every `t`:
* **block endpoint**: after some `t'` host steps with `t ≤ t' ≤ C · (ℓ + 1) · t` the host
  presents the source's configuration after `t` steps, with a correct tag;
* **exit cut**: if the source is live before `t`, the host is live before `t'`;
* **intermediate frames**: at every host time up to `t'`, the bank tapes, the bank heads and
  the output are the source's at some source time no later than `t`, the ruler tape is
  unchanged, and the ruler head is on the ruler or one of its two delimiters;
* **space ledger**: the bank heads visit exactly the source's cells, and the ruler head
  `ℓ + 2` cells.

So the host halts exactly when the source does (the cut and `t ≤ t'` give the converse), with
the source's output, using the source's space plus `ℓ + 2` cells, within `C · (ℓ + 1)` times
the source's time. Literal lockstep (`t' = t`) is the native special case, and Z1's
`Turing.vhostEmitTM`. This is how H2's step block, whose input is native, runs on a suffix
input unchanged. [AB09, §1.2; Exercise 4.1]

**Proof sketch.** Each host step performs the source transition, reading the native symbol, or
blank when the tag is set, and suppressing a left move when the tag is set. A right move
clears the tag; after a left move from a cleared tag the host pauses for the boundary test of
`Turing.exists_rulerTestTM` (on the ruler tape, by R1) and sets the tag from its verdict. A
halting source transition halts the host in the same step, with no pause. The pause costs
`C · (ℓ + 1)` steps, moves no bank head, writes nothing and emits nothing, which gives the
frames and the cut. Induct on `t` as `Turing.vhostEmitTM_runFrom` does; the visited-set clauses
follow `Turing.vhostEmitTM_visitedByTapeHead_bank` and
`Turing.vhostEmitTM_visitedByTapeHead_buffer`.

**Implementation status.** The restoring boundary test and both call rows are proved. The
source-step transformer, its bounded pauses, and the block simulation remain to be assembled.
-/
theorem exists_rulerHostTM {m : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (M : MultiTapeTM m Bool S) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (m + 1) Bool Q)
      (inj : S → Bool → Q) (C : ℕ), 0 < C ∧
      ∀ {y z : List Bool} (ℓ : ℕ) (hz : z.length = ℓ + y.length), 0 < ℓ → z.drop ℓ = y →
      ∀ (rt : ℤ → Option Bool) (rp : ℤ),
        (∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
          rt (rp + p) = FinTM.bufferTape (List.replicate ℓ true) p) →
      ∀ (c : Cfg m Bool S y) (b : Bool), (b = true ↔ c.inputPos.val = 0) → ∀ t : ℕ,
        let d := rulerHostCfg ℓ hz (c.state.map fun q => inj q b) c rt rp
        ∃ t', t ≤ t' ∧ t' ≤ C * (ℓ + 1) * t ∧
          (∃ b' : Bool, (b' = true ↔ (M.runFrom c t).inputPos.val = 0) ∧
            H.runFrom d t' =
              rulerHostCfg ℓ hz ((M.runFrom c t).state.map fun q => inj q b')
                (M.runFrom c t) rt rp) ∧
          ((∀ u < t, (M.runFrom c u).state ≠ none) → ∀ u < t', (H.runFrom d u).state ≠ none) ∧
          (∀ u ≤ t', ∃ v ≤ t,
            (∀ i : Fin m, (H.runFrom d u).workTapes i.castSucc = (M.runFrom c v).workTapes i ∧
              (H.runFrom d u).workTapePos i.castSucc = (M.runFrom c v).workTapePos i) ∧
            (H.runFrom d u).output = (M.runFrom c v).output ∧
            (H.runFrom d u).workTapes (Fin.last m) = rt ∧
            (H.runFrom d u).workTapePos (Fin.last m) ∈ Finset.Icc (rp - 1) (rp + ℓ)) ∧
          (∀ i : Fin m, H.visitedByTapeHead d t' i.castSucc = M.visitedByTapeHead c t i) ∧
          H.visitedByTapeHead d t' (Fin.last m) ⊆ Finset.Icc (rp - 1) (rp + ℓ) := by
  sorry

end Turing
