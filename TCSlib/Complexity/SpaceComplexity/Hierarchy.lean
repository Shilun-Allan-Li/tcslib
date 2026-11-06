/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.SpaceComplexity.WindowClock
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with the space-bounded universal machine of
[AB09, Exercise 4.1] (its forward clause, as the book states it), the
strictness corollary `L ⊊ PSPACE` on the p. 92 chain, and `SPACE(n+1) ≠ NP`
([AB09, Exercise 3.2], stated with the positive normalization). The universal
machine statement has a forward clause with the addend-free bound `C · s`;
the hierarchy uses a fixed self-application universal machine inside a
space-bounded configuration window.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and the layout
  `⟨bits s, ⟨α, x⟩⟩`, and keeps only Exercise 4.1's forward clause: a run of
  the coded machine within `s` work cells is reproduced, output included,
  within constant-factor space. Overruns and divergence are unconstrained, so
  the machine tests no budget, runs no clock and replays nothing. Its space
  bound is Exercise 4.1's `C_α · t`, with no addend: the simulated input, a
  suffix of its input, is read through the bounded-prefix ruler device
  (`Turing.exists_rulerHostTM`), a unary ruler of the header's length, which
  the bound absorbs because every qualifying run visits a cell.
* **The hierarchy takes the window route**: the
  diagonalizer runs one fixed self-application universal machine `U₀` in a
  window of radius `a · g(n)` on the configuration-record rows
  (`Build/CfgRecord.lean`, `Build/RecordTable.lean`), stopped by a
  configuration-count clock, and flips its verdict. The window, not `U₀`'s
  code-dependent constant, bounds the diagonalizer's space. The chapter-1
  interpreter (`Turing.universalInterpreter`) serves neither machine: it
  tracks the simulated input head in unary on its fourth tape, which uses one
  plus the largest simulated input position reached, `Θ(n + 1)` cells on a
  full scan, so it cannot guarantee `O(S(n))` space uniformly for sublinear
  `S`.
* **Both bounds space-constructible**, as in the book; `g`'s witness drives
  the window radius and the clock width, and of `f` the proof uses only the
  bundled floor `1 ≤ logSpace n ≤ f n`.
* The `SpaceComplexity.lean` facade imports this module.

## Main results

* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause
  (restated 2026-10-12; addend-free `C · s` since 2026-10-13).
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-- **The space-bounded universal machine** ([AB09, Exercise 4.1], p. 93,
forward clause; spec, fill pending — phase P4.3, restated forward-only
2026-10-12 by design §16b item 3, RD-3 statement gate passed 2026-10-13;
strengthened to the addend-free `C · s` 2026-10-13, statement gate passed
2026-10-14):
for the fixed scheme there is a machine `SU` such that for every code `α`
there is a constant `C > 0` with: whenever the coded machine halts on `x`
with `output`, having visited at most `s` work cells by then, `SU` on input
`⟨bits s, ⟨α, x⟩⟩` halts with the same `output`, having visited at most
`C · s` work cells: the book's `C · t`. Nothing is claimed when the coded
machine overruns `s` or does not halt. The time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound. Every
qualifying run has `s ≥ 1` (`Turing.CodeTM.one_le_spaceUsed`), so the bound
is never `0`.

Deviations from the book's `SU(α, t, x) = M_α(x)` within `C · t` cells:
* **`C` depends on the representation `α`**, not only on `M_α`, as in
  `Turing.universal`, whose module docstring records why an arbitrary
  effective scheme forces this.
* "Halts before using `t` cells" is read as "at most `s` visited cells"; the
  budget is an argument of `SU`, as in the book, but is never read.
* The output is the simulated output itself: with no failure clause there is
  no verdict to tag. The former `[false]` clause, and with it the
  visited-interval counters, the core-count clock and the probe/replay of the
  previous statement, went with design §16b item 3.

There is no input-device addend: the gated `+ logSpace |x| + 1` (a binary
position for the simulated input head) is replaced by a unary ruler of the
header's length, whose cells the bound absorbs (the RD-3 gate's minor 1).

**Proof sketch.** A code-first interpreter in three parts. (i) **Startup.**
Parse the header `bits s`, `α` and the two separators by a finite-state pair
scan, writing one ruler cell per header cell, so that the ruler is `true^ℓ`
with `ℓ = 2|bits s| + 2|α| + 4` (`Turing.pairEncode_pairEncode_length`,
`Turing.pairEncode_pairEncode_drop`) and the physical input head ends at
`ℓ + 1`, the virtual position `1`; the budget is never read. Canonize `α`
into the table and state tapes as `U₀`'s startup does
(`Turing.exists_selfStartupTM`'s phases, reading the code where the header
holds it). Its cells are a constant depending only on `α`
(`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's halting time);
the effective scheme supplies no bound linear in `|α|`, and none is claimed.
(ii) **Input device and step block** (H5's bounded-prefix ruler device and
H2). Run `U₀`'s wrapped round loop (`Turing.exists_selfUniversal`'s sketch:
H2's step block on the output-erased source, with the leaf that forwards each
emission before the next round and before the halt) through the ruler host
`Turing.exists_rulerHostTM` on the virtual input `x`. The host is a positive
finite block simulation: it reads a blank and suppresses left moves at the
virtual left boundary, which it tests by restoring sweeps of `ℓ` cells
(`Turing.exists_rulerTestTM`), so `SU` halts exactly when the round loop does,
with its output, the coded machine's. The chapter-1 interpreter's device
cannot serve: its fourth tape holds a unary boundary marker whose head
`applyRecord` moves with the input head (`Turing.universalInterpreter`), so
that tape uses one plus the largest simulated input position reached,
`Θ(|x| + 1)` cells on a full scan, which a budget `s = o(|x|)` does not
cover (Finding B). (iii) **Space.** The host's bank visits exactly the round
loop's cells: the mirrored tape only the coded machine's, at most `s`, and the
table and summary tapes `O(|table| + 1)`, a constant for fixed `α`. Its ruler
visits `ℓ + 2` cells. Every qualifying run has `s ≥ 1`
(`Turing.CodeTM.one_le_spaceUsed`) and `|bits s| ≤ s`
(`Turing.length_bits_le_self`), so `ℓ ≤ 2s + 2|α| + 4 ≤ (2|α| + 6) · s`, and
the total `C_α + s + ℓ + 2` is at most `C · s`. Fill obligations, named: the
header-ruler startup with the buffered canonization; the H5 ruler host;
`U₀`'s wrapped round loop (H2 at one coded work tape, with its head
envelope); the per-code constant ledger. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x output : List Bool) (t : ℕ),
        ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
        ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
            (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x)) output t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * s := by
  sorry

/-- The inclusion half: `hfg` at `A = 1` from some `N` on, and `g`'s floor below `N`.
[AB09, Theorem 4.8, inclusion]

**Proof sketch.** Bound the finitely many exceptional values by their supremum. The positive
floor of `g` absorbs that supremum into one constant, and `SPACE.mono_const` applies. -/
private lemma sph_inclusion {f g : ℕ → ℕ} (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) : SPACE f ⊆ SPACE g := by
  obtain ⟨N, hN⟩ := hfg 1
  have hfloor : ∀ n, 1 ≤ g n := fun n =>
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff g).mp hg).1 n)
  set F := (Finset.range N).sup f with hF
  refine SPACE.mono_const (a := F + 1) fun n => ?_
  by_cases hn : N ≤ n
  · have := hN n hn
    calc f n ≤ g n := by simpa using this
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · have hle : f n ≤ F := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
    calc f n ≤ F + 1 := by omega
      _ = (F + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (F + 1) * g n := Nat.mul_le_mul_left _ (hfloor n)

/-- A decider in the smaller space class has a padded code on which the fixed universal
machine halts inside the larger window, before its configuration-count clock expires.
[AB09, Theorem 4.8, diagonal contradiction]

**Proof sketch.** Normalize the decider to one binary work tape and then to a coded machine,
using the published space clauses. Choose the domination constant after the code's universal
simulation constant is fixed, and pad the payload to the resulting threshold. The configuration
bound supplies a halting time; the window-summary theorem identifies the run at the next round. -/
private lemma sph_code_window (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) (U₀ : FinTM Bool)
    (hU : ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (TimeHierarchy.code.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
          ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
        ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
          U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1))
    (L : Language Bool) (c₀ : ℕ) (M : FinTM Bool)
    (hM : M.DecidesInSpace L (fun n => c₀ * f n)) :
    ∃ (x : List Bool) (t : ℕ),
      U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t ∧
      U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length ∧
      t = U₀.configBound x.length (g x.length) ∧
      windowRun U₀.tm (g x.length) summaryTag (t + 1) (U₀.tm.initCfg x) 0 =
        (.halted, U₀.tm.runFrom (U₀.tm.initCfg x) t,
          outSummaryCode (outSummary [MultiTapeTM.indicator (L : Set (List Bool)) x])) := by
  have hm := (FinTM.decidesInSpace_iff M L (fun n => c₀ * f n)).mp hM
  have hbounds := hm.computesFunInTime_and_forall_spaceUsed_le
  obtain ⟨M₁, c₁, hk, htime, hspace⟩ := FinTM.one_work_tape_binary_spaceUsed M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
    (fun n => M.configBound n (c₀ * f n)) (fun n => c₀ * f n) hbounds.1 hbounds.2
  obtain ⟨N, hrun, hsp⟩ := exists_codeTM_spaceUsed M₁ hk
  let α := TimeHierarchy.code.encode N
  have hα : TimeHierarchy.code.decode α = N := MachineCode.decode_encode _ _
  obtain ⟨C, _hC, hsim⟩ := hU α
  let A := C * (c₁ * c₀ + c₁ + 1)
  obtain ⟨N₀, hN₀⟩ := hfg A
  let x := pairEncode α (List.replicate N₀ true)
  have hx : N₀ ≤ x.length := by
    simp only [x, length_pairEncode, List.length_replicate]
    omega
  let t₀ := c₁ * (M.configBound x.length (c₀ * f x.length) + 1) ^ 2
  have hn : (TimeHierarchy.code.decode α).toFinTM.ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ := by
    rw [hα]
    exact (hrun x _ t₀).mpr ((FinTM.computesFunInTime_iff _ _ _).mp htime x)
  have hs : (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
      ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg x) t₀ ≤
      c₁ * (c₀ * f x.length + 1) := by
    rw [hα, hsp]
    exact hspace x t₀
  obtain ⟨u, hu, hsu⟩ := hsim (List.replicate N₀ true)
    [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ (c₁ * (c₀ * f x.length + 1)) hn hs
  have hfloor : 1 ≤ f x.length :=
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff f).mp hf).1 x.length)
  have hsmall : C * (c₁ * (c₀ * f x.length + 1) + 1) ≤ A * f x.length := by
    calc
      _ ≤ C * (c₁ * (c₀ * f x.length + f x.length) + f x.length) :=
        Nat.mul_le_mul_left C (Nat.add_le_add
          (Nat.mul_le_mul_left c₁ (Nat.add_le_add_left hfloor _)) hfloor)
      _ = A * f x.length := by dsimp only [A]; ring
  have hwindow : U₀.tm.spaceUsed (U₀.tm.initCfg x) u ≤ g x.length :=
    hsu.trans (hsmall.trans (hN₀ x.length hx))
  let t := U₀.configBound x.length (g x.length)
  have hhalt : U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t :=
    hu.of_spaceUsed_le hwindow
  have hspace' : U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length :=
    hu.spaceUsed_le_of_halt hwindow t
  exact ⟨x, t, hhalt, hspace', rfl,
    windowRun_summary_of_halts U₀ x hhalt hspace' (Nat.lt_succ_self t)⟩

/-- A square below a power of two, from `4` on.

**Proof sketch.** Induct from `4`; doubling the previous power absorbs the next square. -/
private lemma sph_sq_le_two_pow : ∀ L, 4 ≤ L → L * L ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

/-- The logarithm is dominated by the identity at every constant factor, eventually.

**Proof sketch.** Beyond `2 ^ max 4 (2 * A)`, the integer logarithm is at least both `4` and
`2 * A`. Its square fits below `n`, and dominates `A * (log₂ n + 1)`. -/
private lemma sph_logSpace_dom : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logSpace n ≤ n + 1 := by
  intro A
  refine ⟨2 ^ (max 4 (2 * A)), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := max 4 (2 * A)); omega
  set L := Nat.log 2 n with hL
  have hLge : max 4 (2 * A) ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hsq := sph_sq_le_two_pow L (le_trans (le_max_left _ _) hLge)
  have h2A : 2 * A ≤ L := le_trans (le_max_right _ _) hLge
  rw [logSpace_eq, ← hL]
  nlinarith

/-- **`LOGSPACE ⊂ PSPACE`**, from the space hierarchy's statement. [AB09, §4.3.2]

**Proof sketch.** Apply the hierarchy to logarithmic and linear space, then transport strictness
along the published inclusion of linear space into polynomial space. -/
private lemma sph_logspace_ssubset
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g) :
    LOGSPACE ⊂ PSPACE := by
  have hlin : SPACE (fun n => n + 1) ⊆ PSPACE := by
    have := space_poly_subset_PSPACE 1
    simpa only [pow_one] using this
  obtain ⟨-, hnot⟩ := hH logSpace (fun n => n + 1) spaceConstructible_logSpace
    spaceConstructible_linear sph_logSpace_dom
  refine ⟨LOGSPACE_subset_PSPACE, fun hP => hnot ?_⟩
  rw [← LOGSPACE_eq]
  exact hlin.trans hP

/-- One input-head move before the lifted rewind. The rewind's published contract requires a
positive input position; this leaf supplies it even when the radius witness stops at `0`.
The action changes no work tape or output. [AB09, §1.2]

**Proof sketch.** The transition always moves the input head right and reaches its live anchor.
At the right boundary it stays put; everywhere else its position increases by one. -/
private def sphRightTM (k : ℕ) (Γ : Type) : MultiTapeTM k Γ Bool where
  q₀ := false
  tr := fun _ _ _ => ⟨.pos, fun _ => (none, 0), none, some true⟩

/-- The right-move leaf's framed run and positive endpoint.

**Proof sketch.** Read the one transition field by field, separate the input's right boundary,
and use the zero-step and one-step configurations for the cut and head claim. -/
private lemma sph_right_run {k : ℕ} {Γ : Type} {x : List Γ}
    (d : Cfg k Γ Bool x) (hd : d.state = some false) :
    (sphRightTM k Γ).runFrom d 1 =
        {d with state := some true, inputPos := moveInputPos d.inputPos .pos} ∧
      1 ≤ (moveInputPos d.inputPos .pos).val ∧
      (∀ u < 1, ((sphRightTM k Γ).runFrom d u).state ≠ some true) ∧
      ∀ u ≤ 1, ((sphRightTM k Γ).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphRightTM k Γ).runFrom d 1 =
      {d with state := some true, inputPos := moveInputPos d.inputPos .pos} := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]; rfl
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphRightTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphRightTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      simp only [sphRightTM, Option.toList_none, List.append_nil]
  refine ⟨hstep, ?_, ?_, ?_⟩
  · by_cases h : d.inputPos.val = x.length + 1
    · have hp : d.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h
      rw [hp, SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right _ h]
      exact Nat.succ_pos _
  · intro u hu
    have : u = 0 := by omega
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    decide
  · intro u hu
    have : u = 0 ∨ u = 1 := by omega
    rcases this with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · rw [hstep]

/-- Emit the final verdict and halt, preserving the input and work tapes. The only output
leaf needed after the record test. [AB09, §1.2] -/
private def sphEmitTM (k : ℕ) {Γ : Type} (b : Γ) : MultiTapeTM k Γ Unit where
  q₀ := ()
  tr := fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩

/-- The verdict emitter appends exactly one symbol in one step, with no work-head motion.

**Proof sketch.** Read the five fields of its sole action using the public action equations. -/
private lemma sph_emit_run {k : ℕ} {Γ : Type} {x : List Γ} (b : Γ)
    (d : Cfg k Γ Unit x) (hd : d.state = some ()) :
    (sphEmitTM k b).runFrom d 1 = {d with state := none, output := d.output ++ [b]} ∧
      ∀ u ≤ 1, ((sphEmitTM k b).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphEmitTM k b).runFrom d 1 =
      {d with state := none, output := d.output ++ [b]} := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]
      exact moveInputPos_zero _
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphEmitTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphEmitTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      rfl
  refine ⟨hstep, ?_⟩
  intro u hu
  have : u = 0 ∨ u = 1 := by omega
  rcases this with rfl | rfl
  · rw [MultiTapeTM.runFrom_zero]
  · rw [hstep]

/-- The input validator's finite-state test: precisely the embedded binary digits. -/
private def sphDigit {Q : Type} : RecSym Q (Fin 3) → Bool
  | .digit _ => true
  | .cell _ _ => false
  | .st _ => false
  | .tag _ => false

/-- The validator accepts precisely embedded binary words, including the empty word.

**Proof sketch.** Induct on the input. A successful fold forces the head symbol to be a digit;
strip that digit and use the induction hypothesis on the tail. Conversely, prepend the
corresponding Boolean to the decoded tail. -/
private lemma sph_fold_valid {Q : Type} (ys : List (RecSym Q (Fin 3))) (a : Bool) :
    ys.foldl (fun b c => b && sphDigit c) a = true ↔
      a = true ∧ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) := by
  induction ys generalizing a with
  | nil =>
    rw [List.foldl_nil]
    exact ⟨fun h => ⟨h, [], rfl⟩, fun h => h.1⟩
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨hay, x, hx⟩
      obtain ⟨ha, hy⟩ := Bool.and_eq_true_iff.mp hay
      refine ⟨ha, ?_⟩
      cases y with
      | digit b =>
        refine ⟨b :: x, ?_⟩
        rw [List.map_cons, RecSym.digitEmb_apply, ← hx]
      | cell c m => cases hy
      | st q => cases hy
      | tag t => cases hy
    · rintro ⟨ha, x, hx⟩
      cases x with
      | nil => cases hx
      | cons b bs =>
        rw [List.map_cons] at hx
        obtain ⟨hy, ht⟩ := List.cons.inj hx
        refine ⟨Bool.and_eq_true_iff.mpr ⟨ha, ?_⟩, bs, ht⟩
        rw [hy, RecSym.digitEmb_apply]
        rfl

/-- The rich-input validation phase, on all of the diagonalizer's work tapes. Its successful
exit supplies a binary input for every subsequent phase; it moves no work head.
[AB09, Theorem 4.8, alphabet reduction]

**Proof sketch.** Use the published framed input fold and identify its final flag with
`sph_fold_valid`. The framed endpoint also restores the input head to its initial position. -/
private lemma sph_validation_run {k : ℕ} {Q : Type}
    {ys : List (RecSym Q (Fin 3))} (d : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys)
    (hd : d.state = some (.fwd true)) (hin : d.inputPos = 1) :
    ∃ b : Bool,
      (inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d (2 * ys.length + 2) =
        {d with state := some (.done b)} ∧
      (b = true ↔ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3))) ∧
      (∀ u < 2 * ys.length + 2, ∀ a,
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).state ≠
          some (.done a)) ∧
      ∀ j u, u ≤ 2 * ys.length + 2 →
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).workTapePos j =
          d.workTapePos j := by
  obtain ⟨hr, hc, hh⟩ := inputFoldTM_run_ofCfg (fun a c => a && sphDigit c) true d hd hin
  refine ⟨ys.foldl (fun a c => a && sphDigit c) true, hr, ?_, hc, hh⟩
  exact ⟨fun h => ((sph_fold_valid ys true).mp h).2,
    fun h => (sph_fold_valid ys true).mpr ⟨rfl, h⟩⟩

/-- Witness tapes are after the record, radius, initializer scratch and runner scratch banks.
Separate scratch banks keep the runner disjoint from both the radius and the dirty witness. -/
private def sphWitnessSel (KI KR m : ℕ) : Fin m ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨KI + KR + 2 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : KI + KR + 2 + i.val = KI + KR + 2 + j.val :=
      congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h
    omega

/-- The radius tape is outside the witness bank, including for a zero-tape witness. -/
private lemma sph_witness_cap (KI KR m : ℕ) :
    (1 : Fin (KI + KR + m + 2)) ∉ Set.range (sphWitnessSel KI KR m) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [sphWitnessSel, Function.Embedding.coeFn_mk, Fin.val_one] at this
  omega

/-- The constructibility witness returns with its complete binary radius on tape `1`, preserving
all tapes outside its bank and the radius tape. Its last emission is included in the captured
word. [AB09, Theorem 4.8, radius phase]

**Proof sketch.** Choose the witness's first halting time and lift its run to the record
alphabet. Apply the published returning capture embedding. Its capture and frame equations give
the endpoint. Its selected, capture and frame space equations bound each tape; summing gives a
constant multiple of the witness space and radius length. -/
private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
    (g : ℕ → ℕ) (c : ℕ) (M : FinTM Bool)
    (hM : M.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n))
    (x : List Bool)
    (tapes : Fin (KI + KR + M.k + 2) → ℤ → Option (RecSym Q (Fin 3)))
    (heads : Fin (KI + KR + M.k + 2) → ℤ) (out : List (RecSym Q (Fin 3))) :
    let e := RecSym.digitEmb Q (Fin 3)
    let ι := sphWitnessSel KI KR M.k
    let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
    let start := (embedSilentCfg ι 1 tapes heads [] out
      ((M.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : M.State → M.State ⊕ Unit)
    ∃ t : ℕ,
      (R.runFrom start t).state = some (Sum.inr ()) ∧
      (∀ u < t, (R.runFrom start u).state ≠ some (Sum.inr ())) ∧
      (R.runFrom start t).workTapes 1 =
        FinTM.bufferTape ((g x.length).bits.map RecSym.digit) ∧
      (R.runFrom start t).workTapePos 1 = ((g x.length).bits.length : ℤ) ∧
      (∀ j, j ∉ Set.range ι → j ≠ 1 →
        (R.runFrom start t).workTapes j = tapes j ∧
          (R.runFrom start t).workTapePos j = heads j) ∧
      (∀ u ≤ t, (R.runFrom start u).output = out) ∧
      R.spaceUsed start t ≤ (KI + KR + M.k + 2) *
        (c * g x.length + (g x.length).bits.length + 1) := by
  classical
  dsimp only
  let e := RecSym.digitEmb Q (Fin 3)
  let ι := sphWitnessSel KI KR M.k
  let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
  let a := (M.tm.initCfg x).liftSymbols e
  let start := (embedSilentCfg ι 1 tapes heads [] out a).mapState
    (Sum.inl : M.State → M.State ⊕ Unit)
  obtain ⟨v, hv, hsv⟩ := (FinTM.computesInSpace_iff _ _ _).mp hM x
  obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hv
  obtain ⟨t, htv, hlive, heq⟩ := M.tm.exists_first_halt (M.tm.initCfg x) hhalt
  have hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * g x.length :=
    (M.tm.spaceUsed_mono _ htv).trans hsv
  have ho : (M.tm.runFrom (M.tm.initCfg x) t).output = (g x.length).bits :=
    (congrArg Cfg.output heq).trans hout
  have hc : a.state ≠ none := by
    rw [Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hh : ((M.tm.liftSymbols e).runFrom a t).state = none := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state, heq, hhalt]
  have hl : ∀ u < t, ((M.tm.liftSymbols e).runFrom a u).state ≠ none := by
    intro u hu
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state]
    exact hlive u hu
  have hcap := sph_witness_cap KI KR M.k
  obtain ⟨hpre, hr, hcut⟩ := embedSilentRetTM_run ι 1 hcap (M.tm.liftSymbols e)
    tapes heads [] out a t hc hl hh
  have hout' : ((M.tm.liftSymbols e).runFrom a t).output =
      (g x.length).bits.map RecSym.digit := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output, ho]
    apply List.map_congr_left
    intro b _
    exact RecSym.digitEmb_apply _ _ b
  refine ⟨t, ?_, hcut, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).1
    simpa only [List.nil_append, hout'] using h
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).2
    simpa only [List.nil_append, hout', List.length_map] using h
  · intro j hj hjc
    rw [hr]
    exact embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc
  · intro u hu
    rcases lt_or_eq_of_le hu with hu | rfl
    · rw [hpre u hu, Cfg.mapState_output, embedSilentCfg_output]
    · rw [hr, embedSilentCfg_output]
  · rw [MultiTapeTM.spaceUsed_eq_sum]
    calc
      _ ≤ ∑ _j : Fin (KI + KR + M.k + 2),
          (c * g x.length + (g x.length).bits.length + 1) := by
        apply Finset.sum_le_sum
        intro j _
        rw [MultiTapeTM.spaceUsedByTape_eq_card,
          embedSilentRetTM_visitedByTapeHead,
          ← MultiTapeTM.spaceUsedByTape_eq_card]
        by_cases hj : j ∈ Set.range ι
        · obtain ⟨i, rfl⟩ := hj
          rw [(embedSilentTM_visitedByTapeHead ι 1 hcap _ tapes heads [] out a t i).2]
          have h : (M.tm.liftSymbols e).spaceUsedByTape a t i ≤ c * g x.length :=
            calc
              _ ≤ (M.tm.liftSymbols e).spaceUsed a t :=
                (M.tm.liftSymbols e).spaceUsedByTape_le_spaceUsed a t i
              _ = M.tm.spaceUsed (M.tm.initCfg x) t :=
                MultiTapeTM.liftSymbols_spaceUsed M.tm e (M.tm.initCfg x) t
              _ ≤ _ := hs
          omega
        · by_cases hjc : j = 1
          · subst j
            have h := embedSilentTM_spaceUsedByTape_cap ι 1 hcap
              (M.tm.liftSymbols e) tapes heads [] out a t
            rw [hout', List.length_map] at h
            exact h.trans (by omega)
          · rw [(embedSilentTM_visitedByTapeHead_frame ι 1 hcap _
              tapes heads [] out a t j hj hjc).2]
            omega
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rfl

/-- The input rewind uses no work tapes, so its embedding preserves every work tape. -/
private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k where
  toFun := Fin.elim0
  inj' := fun i => Fin.elim0 i

/-- The lifted binary input rewind, embedded on the empty bank, is valid from any positive
input position of an embedded binary word, with the entire physical work bank framed.

**Proof sketch.** Construct the zero-tape binary configuration at the same input position,
apply the published input rewind, lift its run, and use the R1 reconstruction theorem to
identify its initial and final embeddings with the physical configurations. -/
private lemma sph_input_rewind_run {k : ℕ} {Q : Type} [DecidableEq Q] {x : List Bool}
    (d : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some .start) (hp : 1 ≤ d.inputPos.val) :
    let R := embedEmitTM (sphEmptySel k)
      ((inputRewindTM 0).liftSymbols (RecSym.digitEmb Q (Fin 3)))
    R.runFrom d (d.inputPos.val + 1) = {d with state := some .done, inputPos := 1} ∧
      (∀ u < d.inputPos.val + 1, (R.runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 1, (R.runFrom d u).workTapePos = d.workTapePos := by
  let e := RecSym.digitEmb Q (Fin 3)
  let a : Cfg 0 Bool InputRewindPhase x :=
    ⟨some .start, ⟨d.inputPos.val, by simpa only [List.length_map] using d.inputPos.isLt⟩,
      Fin.elim0, Fin.elim0, []⟩
  have ha : a.inputPos.val = d.inputPos.val := rfl
  have hi : (a.liftSymbols e).inputPos = d.inputPos := by
    rw [Cfg.liftSymbols_inputPos]
    exact Fin.ext rfl
  have hs : embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
      (a.liftSymbols e) = d := by
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]; exact hd.symm
    · exact hi
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  obtain ⟨hr, hc, hh⟩ := inputRewindTM_run a rfl (ha.symm ▸ hp)
  have hrun (u : ℕ) :
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)).runFrom d u =
        embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
          (((inputRewindTM 0).runFrom a u).liftSymbols e) := by
    have h := embedEmitTM_runFrom (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
      d.workTapes d.workTapePos d.output (a.liftSymbols e) u
    rw [hs, MultiTapeTM.liftSymbols_runFrom] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, ← ha, hr]
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]
    · rw [Cfg.liftSymbols_inputPos]
      exact Fin.ext rfl
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state, Cfg.liftSymbols_state]
    exact hc u (ha.symm ▸ hu)
  · intro u _
    rw [hrun]
    funext j
    exact (embedEmitCfg_unselected (sphEmptySel k) d.workTapes d.workTapePos d.output
      (((inputRewindTM 0).runFrom a u).liftSymbols e) j
      (by rintro ⟨i, _⟩; exact Fin.elim0 i)).2

/-- The two rewinds after radius capture: a right move makes the input position positive,
the zero-tape input rewind restores position one, and the radius rewind restores tape one.
Both seams use the published general-configuration composition. -/
private def sphRewindsTM (k : ℕ) (Q : Type) [DecidableEq Q] (cap : Fin k) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) :=
  seamCompTM
    (seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols
        (RecSym.digitEmb Q (Fin 3)))) .start)
    (.inr .done) (rewindTM k cap) .start

/-- The paired rewinds on the tape plan, including an empty captured word and an input head
initially at zero. Every work-tape cell and the accumulated output are preserved.

**Proof sketch.** Compose the one-step right move and the lifted zero-tape rewind at their
first returns. Apply the framed radius rewind at the full captured word's length and compose
again. Read the endpoint through the public state-map equations. -/
private lemma sph_rewinds_run (KI KR m : ℕ) {Q : Type} [DecidableEq Q]
    {x : List Bool} (ws : List Bool)
    (d : Cfg (KI + KR + m + 2) (RecSym Q (Fin 3)) Bool
      (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some false)
    (hcap : d.workTapes 1 = FinTM.bufferTape (ws.map RecSym.digit))
    (hpos : d.workTapePos 1 = (ws.length : ℤ)) :
    ∃ t,
      (sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) t =
        { state := some (Sum.inr RewindPhase.done)
          inputPos := 1
          workTapes := d.workTapes
          workTapePos := Function.update d.workTapePos 1 0
          output := d.output } ∧
      ∀ u < t,
        ((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).state ≠ some (Sum.inr .done) := by
  let k := KI + KR + m + 2
  let e := RecSym.digitEmb Q (Fin 3)
  let I := embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
  let A := seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true I .start
  let d₁ := {d with state := some true, inputPos := moveInputPos d.inputPos .pos}
  let a := d₁.mapState (fun _ => InputRewindPhase.start)
  let d₂ : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map e) :=
    {a with state := some InputRewindPhase.done, inputPos := 1}
  obtain ⟨h₁, hp, hc₁, _⟩ := sph_right_run d hd
  obtain ⟨h₂, hc₂, _⟩ := sph_input_rewind_run a
    (by rw [Cfg.mapState_state]; rfl)
    (by rw [Cfg.mapState_inputPos]; exact hp)
  have hA : A.runFrom (d.mapState Sum.inl) (1 + 1 + (a.inputPos.val + 1)) =
      d₂.mapState Sum.inr :=
    seamCompTM_run_ofCfg (sphRightTM k _) true I .start h₁ rfl hc₁ h₂
  have hAc := seamCompTM_firstReturn_ofCfg (sphRightTM k _) true I .start .done
    h₁ rfl hc₁ h₂ rfl hc₂
  let b := (d₂.mapState (Sum.inr : InputRewindPhase → Bool ⊕ InputRewindPhase)).mapState
    (fun _ => RewindPhase.start)
  have hb : b.state = some .start := by
    rw [Cfg.mapState_state, Cfg.mapState_state]
    rfl
  have hbh : b.workTapePos = d.workTapePos := by
    funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  have hbt : b.workTapes = d.workTapes := by
    funext j p
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  obtain ⟨h₃, hc₃, _⟩ := rewindTM_run_ofCfg (1 : Fin k)
    (ws.map (RecSym.digit : Bool → RecSym Q (Fin 3))) ws.length
    (by rw [List.length_map]) b hb (by
      intro p _ _
      rw [hbt, hbh, hpos, sub_self, zero_add, hcap])
  let d₃ := { b with
    state := some RewindPhase.done
    workTapePos := Function.update b.workTapePos 1 (b.workTapePos 1 - ws.length) }
  have hend : d₃.mapState Sum.inr =
      ({ state := some (Sum.inr RewindPhase.done)
         inputPos := 1
         workTapes := d.workTapes
         workTapePos := Function.update d.workTapePos 1 0
         output := d.output } : Cfg k (RecSym Q (Fin 3))
           ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) (x.map e)) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j p
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun hbt j) p
    · funext j
      rw [Cfg.mapState_workTapePos]
      dsimp only [d₃]
      rw [hbh, hpos, sub_self]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output]
  refine ⟨(1 + 1 + (a.inputPos.val + 1)) + 1 + (ws.length + 2), ?_, ?_⟩
  · exact (seamCompTM_run_ofCfg A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃).trans hend
  · exact seamCompTM_firstReturn_ofCfg A (.inr .done) (rewindTM k 1) .start .done
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃ rfl hc₃

/-- The record initializer occupies the record, radius and its own contiguous scratch bank. -/
private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨i.val, by have := i.isLt; omega⟩
  inj' := fun _ _ h => Fin.ext
    (congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h)

/-- The initial-record phase on the diagonalizer's tape plan. Only the initializer's scratch
bank must be blank; the witness and runner banks are framed. [AB09, Theorem 4.8]

**Proof sketch.** Select the record, radius and initializer scratch tapes. Read the selected
configuration through the R1 reconstruction equation and its field equations. Apply the
published initial-record row, transport its run by R1 and reconstruct the framed endpoint. -/
private lemma sph_initial_record (M : FinTM Bool) (KR m : ℕ) :
    ∃ (KI : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry exit : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ p : ℤ, -1 ≤ p → p ≤ (recordLength M.k x.length s : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (KI + KR + m + 2), 2 ≤ j.val → j.val < KI + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (recordLength M.k x.length s + ws.length + s + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + (recordLength M.k x.length s : ℤ)
                  then fieldsTape (cfgRecord s (M.tm.initCfg x) 0) (q - d.workTapePos j)
                else d.workTapes j q} := by
  classical
  obtain ⟨KI, P, hF, hD, I, entry, exit, C, hI⟩ :=
    exists_recordInitTM M.k M.tm.q₀ (0 : Fin 3)
  letI := hF
  letI := hD
  let ι := sphInitSel KI KR m
  have h0 : ι 0 = 0 := Fin.ext rfl
  have h1 : ι 1 = 1 := Fin.ext rfl
  refine ⟨KI, P, hF, hD, embedEmitTM ι I, entry, exit, C, ?_⟩
  intro x s ws hws d hd hin hrad hslot hblank
  let a := d.select ι
  have hrecon : embedEmitCfg ι d.workTapes d.workTapePos d.output a = d :=
    embedEmitCfg_select ι d
  have hstate : a.state = d.state := by
    have h := congrArg Cfg.state hrecon
    rwa [embedEmitCfg_state] at h
  have hinput : a.inputPos = d.inputPos := by
    have h := congrArg Cfg.inputPos hrecon
    rwa [embedEmitCfg_inputPos] at h
  have houtput : d.output ++ a.output = d.output := by
    have h := congrArg Cfg.output hrecon
    rwa [embedEmitCfg_output] at h
  have htapes (i : Fin (KI + 2)) : a.workTapes i = d.workTapes (ι i) := by
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output a).workTapes (ι i) =
        d.workTapes (ι i) := congrArg (fun c => c.workTapes (ι i)) hrecon
    rwa [embedEmitCfg_selected_tape] at h
  have hheads (i : Fin (KI + 2)) : a.workTapePos i = d.workTapePos (ι i) := by
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output a).workTapePos (ι i) =
        d.workTapePos (ι i) := congrArg (fun c => c.workTapePos (ι i)) hrecon
    rwa [embedEmitCfg_selected_pos] at h
  obtain ⟨t, htime, hcut, henv, hr⟩ := hI s ws hws a (hstate.trans hd) (hinput.trans hin)
    (by intro p hp hp'; rw [htapes, hheads, h1]; exact hrad p hp hp')
    (by intro p hp hp'; rw [htapes, hheads, h0]; exact hslot p hp hp')
    (by
      intro j hj p
      rw [htapes]
      exact hblank (ι j) hj (by have := j.isLt; exact this) p)
  have hrun (u : ℕ) :
      (embedEmitTM ι I).runFrom d u =
        embedEmitCfg ι d.workTapes d.workTapePos d.output (I.runFrom a u) := by
    have h := embedEmitTM_runFrom ι I d.workTapes d.workTapePos d.output a u
    rwa [hrecon] at h
  refine ⟨t, htime, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [hheads, htapes, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]): for
space-constructible `f` and `g`, if every constant multiple of `f` is
eventually below `g` (that is, `f = o(g)`), then `SPACE f ⊊ SPACE g`.
Constant-factor hypothesis — no square and no logarithmic term, by a
universal simulation with constant-factor space overhead (the
self-application universal `U₀` of the sketch, the sibling of
`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof uses `g`'s witness and floor but, of `f`'s, only the
bundled floor. Positivity of both bounds is automatic from the bundled
`logSpace` floor, so the zero-bound convention needs no side condition.

**Proof sketch.** *Inclusion.* `hfg` at `A = 1` gives `f n ≤ g n` from some
`N` on; below `N` each `f n` is at most `F := max_{n<N} f n` times
`g n ≥ 1` (`g`'s floor), so `f ≤ max F 1 · g` everywhere and
`Complexity.SPACE.mono_const` applies.

*The universal machine `U₀`.* One fixed machine for the scheme
`Complexity.TimeHierarchy.code`: on an input `x = pairEncode α w` it canonizes
`α` from the doubled prefix (the chapter-1 startup, `Turing.universalCanonTM`),
returns its input head to the origin, and simulates the coded machine on `x`
itself — self-application, so no `preTM` copy is needed — with its own input
head as the simulated one (the native device: the simulated input is all of
`U₀`'s input, so its left boundary is a real blank and no position is stored)
and the step block on the canonical table. Its forward ledger: for each
`α` a constant `C_α` such that whenever the coded machine halts on `x` with
some output, having visited at most `s` cells, `U₀` halts on `x` with the
same output, having visited at most `C_α · (s + 1)` cells
(`Turing.exists_selfUniversal`). This is `space_universal`'s forward clause
with the native device in place of the bounded-prefix ruler, so no header
ruler is needed; only this direction is used.

*The diagonalizer `D`.* On input `x` with `n = |x|`, over the record alphabet:
(i) validate the input (`Turing.inputFoldTM`), so that
`D`'s space is bounded on foreign rich inputs, as
`Turing.FinTM.alphabet_reduction_spaceUsed` requires, and compute
`bits (g n)` by `g`'s witness, captured on a work tape, in `O(g n)` cells;
(ii) form the radius `r = a · g n` for a fixed `a ≥ 1`
(`a = 1` suffices, the code-dependent constant being paid by the hypothesis
below; a power of two costs only low zero digits) and write `U₀`'s initial
record on `x` at radius `r`, tagged with the empty-output summary
(`Turing.exists_recordInitTM`); (iii) run the configuration-count windowed runner: each round
tests the record for a halted state (`Turing.exists_recordTestTM`), else
applies one step of `U₀` (`Turing.exists_recordStepTM`, whose `no` verdict
is the window exit), the tag updated by the three-valued output summary
`Turing.outSummary` (append-compatible, `Turing.outSummary_append_congr`;
coded in `Fin 3`), so the emitted word is never buffered. The rounds are driven by
the configuration-count clock,
the rich counter loop (`Turing.counterLoopTMVia`) on an
all-`true` word of width `W = |Q₀| + posWidth n + 3 · k₀ · (2r + 1) + 1`,
where `Q₀` and `k₀` are `U₀`'s states and tape count. Its value `2^W - 1`
exceeds `Turing.FinTM.configBound U₀ n r`, which is at most
`2^(|Q₀| + posWidth n + 3 · k₀ · (2r + 1))`, each of its four factors being
at most a power of two. (iv) Answer `false` if the runner stopped at a halted
record with summary `accept` (output exactly `[true]`,
`Turing.outSummary_eq_accept_iff`), and `true` on every other exit: halted
with another output, window exit, or clock exhaustion. `D` halts on every
input. Its cells are the witness's `O(g n)`, the record's
`k₀ · (2r + 1) + posWidth n + k₀ + 4` (`Turing.recordLength`), the record
rows' `O(record length)` scratch and the clock's `W`: all `O(g n)` with
constants depending only on `U₀` and `g`'s witness, **uniformly in the code
part of `x`**, because the window, not `U₀`'s constant, bounds the
simulation; the `posWidth n = O(logSpace n)` terms are
absorbed by `g`'s floor. After the alphabet reduction, the language `L_D`
that `D` decides lies in `SPACE g`.

*`L_D ∉ SPACE f`.* Suppose `M` decides `L_D` within `c₀ · f n` cells. Then
`M` halts within `configBound M n (c₀ · f n)` steps
(`Turing.FinTM.ComputesInTime.of_spaceUsed_le`), and its space bound holds at
every time (`Turing.MultiTapeTM.spaceUsed_mono` up to the halt, the halted
configuration frozen after it). The space-faithful normal form
`Turing.FinTM.one_work_tape_binary_spaceUsed` gives a one-work-tape binary
`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N`
(`Turing.exists_codeTM`, plus the space clause it does not state:
relabelling states leaves tapes and heads untouched,
`Turing.MultiTapeTM.relabelState_runFrom_init`) and set
`α_M := code.encode N`, so that `code.decode α_M = N`. Pad the **payload**,
never the code: on `x = pairEncode α_M w`, `U₀` outputs `N`'s verdict
`[x ∈ L_D]` within `C_{α_M} · (c · (c₀ · f n + 1) + 1) ≤ A · f n` cells,
where `A := C_{α_M} · (c · c₀ + c + 1)`, using `1 ≤ f n`. The hypothesis
`hfg` at this one `A` gives `N₀` with `A · f n ≤ g n ≤ r` for `n ≥ N₀`;
take `w := List.replicate N₀ true`. Then every configuration of `U₀`'s run
on `x` up to its halt is in the radius-`r` window, since each
tape's visited cells form an interval around `0` of size at most `r`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`) and every nonblank cell was
visited (`Turing.MultiTapeTM.mem_visited_of_ne_none`); and the halt comes by
step `configBound U₀ n r` (`ComputesInTime.of_spaceUsed_le` at the bound
`r`), before the clock runs out. So the runner stops at `U₀`'s halted record,
whose summary is `accept` exactly when `x ∈ L_D`, and `D` answers the
opposite: `x ∈ L_D ↔ x ∉ L_D`, a contradiction. The construction uses
`U₀` with its forward ledger (the step block at one coded work tape, the
native input device and the chapter-1 startup); the configuration-count
windowed runner at `U₀` with the output-summary tag, over the record rows
`exists_recordInitTM` (with `exists_recordTemplateTM` beneath it),
`exists_recordTestTM` and
`exists_recordStepTM`, clocked by `counterLoopTMVia`; the radius and
clock-width phases (`g`'s witness captured, radius digits, width expansion);
the window-containment lemma from the visited-interval facts; the space
clause of `exists_codeTM` and the all-times space bound of a decider; the
contradiction arithmetic; `D`'s `DecidesInSpace` packaging through the
alphabet reduction. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  sorry

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear`; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  exact sph_logspace_ssubset space_hierarchy

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` — the literal `SPACE(n)` is the zero-work-tape class).
Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. `NP` is closed downward
under `≤ₚ` (the chapter-2 bounded-certificate transport — a derived
obligation from `Complexity.mem_NP_iff_exists_length_le`, Exercise 2.1's
bounded form, named for the brief). Padding transfers space bounds down:
for `L ∈ SPACE (n² + 1)`, the padded language
`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate (|x|²) true)}` —
membership restricted to padded members of `L`; padded
length exactly `m = n² + 2n + 2`, syntax validated — lies in `SPACE (m + 1)` in the padded
length (validate, then run the `L`-decider on the first component; the pad
supplies the room — the chapter-2 padding-cluster discipline,
`EXP_subset_NEXP`'s precedent), so `L' ∈ NP` by the assumption, and
`L ≤ₚ L'` by the padding reduction (a `polyUnary` emitter; the **unpadded**
language reduces to the **padded** one), so `L ∈ NP = SPACE (n + 1)` — the
`NP` pullback composing the reduction with the bounded-certificate verifier
at the reduction's polynomial output length. Hence
`SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). Fill obligations, named: the `NP`
`≤ₚ`-closure lemma; the padded-language space decider; the padding
reduction machine; the strictness extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  sorry

end Complexity
