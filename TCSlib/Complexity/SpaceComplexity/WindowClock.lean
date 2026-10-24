/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.SpaceComplexity.ConfigGraph

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The windowed runner under a configuration-count clock

Host H3 (`machine-library-design.md` §14) in the form `Complexity.space_hierarchy`'s
diagonalizer cites: the windowed runner of `Build/WindowRun.lean` with a clock that it builds
itself, large enough for every configuration of the simulated machine in the window plus the
one extra halt-test round ([AB09, §4.1.1, Claim 4.4]). With it come the bridges from space
bounds to windows: a computation within `s` cells stays in the radius-`s` window; the
configuration count is at most a power of two whose exponent is linear in the record length;
and a halting space-bounded computation is reported `halted` by the windowed run, with its
output's summary tag.

The module is in `SpaceComplexity` because it uses `Turing.FinTM.configBound`
(`SpaceComplexity/ConfigCount.lean`) and the summary tag (`SpaceComplexity/ConfigGraph.lean`),
so that `Build/WindowRun.lean` imports nothing from `SpaceComplexity`.

**Status.** The bridges are proved. `Turing.exists_configWindowRunnerTM` is sorried with its
proof sketch; private lemmas toward it (the clock arithmetic at the actual record, the one-cell
move, a field's constant copy and the clock's clear) are proved.

## Main definitions

None: the module uses existing definitions.

## Main results

* `Turing.FinTM.inWindow_of_spaceUsed_le` — window containment (proved).
* `Turing.windowRun_summary_of_halts` — the windowed run of a halting space-bounded
  computation, with the summary tag (proved).
* `Turing.FinTM.configBound_le_two_pow` — the configuration count is at most a power of two
  (proved).
* `Turing.exists_configWindowRunnerTM` — the windowed runner with its configuration-count
  clock (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4: the configuration count; §4.1.3,
  Theorem 4.8, whose proof the book assigns to Exercise 4.1. The runner, its clocks and the
  bridges are the repository's refinement of that argument.)
-/

namespace Turing

/-! ### From space bounds to windows -/

/-- **Window containment.** If `M` has visited at most `s` work cells by time `t` on `x`,
then every configuration of its run up to time `t` lies in the radius-`s` window: every head
is within `[-s, s]` and every cell outside it is blank. This is the containment step of
`Complexity.space_hierarchy`'s contradiction, and the hypothesis under which the windowed
runner follows the run. [AB09, §4.1.1, Claim 4.4]

**Proof sketch.** Each tape's visited set has at most `s` cells and is an interval around `0`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`), so each visited cell has absolute value below
`s`. The head at time `u` is visited, and a nonblank cell at time `u` was visited by then
(`Turing.MultiTapeTM.mem_visited_of_ne_none`), hence by time `t`. -/
theorem FinTM.inWindow_of_spaceUsed_le (M : FinTM Bool) (x : List Bool) {t s : ℕ}
    (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s) :
    ∀ u ≤ t, (M.tm.runFrom (M.tm.initCfg x) u).InWindow s := by
  intro u hu
  have hmem : ∀ i, ∀ z ∈ M.tm.visitedByTapeHead (M.tm.initCfg x) t i, |z| < (s : ℤ) := by
    intro i z hz
    have hcard : (M.tm.visitedByTapeHead (M.tm.initCfg x) t i).card ≤ s :=
      (M.tm.spaceUsedByTape_le_spaceUsed _ t i).trans hs
    exact (M.tm.abs_pos_lt_card_visited x t i hz).trans_le (by exact_mod_cast hcard)
  refine ⟨fun i => (hmem i _ ?_).le, fun i z hz => ?_⟩
  · simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨u, by omega, rfl⟩
  · by_contra hne
    have hv := M.tm.visitedByTapeHead_mono _ hu i (M.tm.mem_visited_of_ne_none x u i z hne)
    have := hmem i z hv
    omega

/-- **The windowed run of a space-bounded halting computation** (the B6 instance). If `M`
halts on `x` with output `w` by time `t`, having visited at most `s` cells, and `t < N`, then
`N` rounds from `M`'s initial configuration with the empty-output tag `0` report exit
`halted`, the halted configuration of time `t`, and the tag of `w`. With the tag `1` exactly
when `w = [true]` (`Turing.outSummaryCode_eq_one_iff`), this is the verdict the diagonalizer
flips. [AB09, Theorem 4.8 with Exercise 4.1]

**Proof sketch.** Window containment (`Turing.FinTM.inWindow_of_spaceUsed_le`), then
`Turing.windowRun_halted_of_run` with `σ = outSummaryCode ∘ outSummary`, whose compatibility
is `Turing.summaryTag_append`. -/
theorem windowRun_summary_of_halts (M : FinTM Bool) (x : List Bool) {w : List Bool}
    {t s N : ℕ} (h : M.ComputesInTime x w t) (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s)
    (hN : t < N) :
    windowRun M.tm s summaryTag N (M.tm.initCfg x) 0 =
      (.halted, M.tm.runFrom (M.tm.initCfg x) t, outSummaryCode (outSummary w)) := by
  obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff M x w t).mp h
  have key := windowRun_halted_of_run M.tm s summaryTag (fun u => outSummaryCode (outSummary u))
    summaryTag_append N t (M.tm.initCfg x) hN hhalt (FinTM.inWindow_of_spaceUsed_le M x hs)
  rw [hout] at key
  exact key

/-- **The configuration count is at most a power of two** (the RD-3 gate's check 4):
`configBound M n s ≤ 2 ^ (|Q| + posWidth n + 3 k (2s + 1))`. Its four factors satisfy
`|Q| + 1 ≤ 2^|Q|`, `n + 2 ≤ 2^(posWidth n)`, `3^(k(2s+1)) ≤ 2^(2k(2s+1))` and
`(2s + 1)^k ≤ 2^(k(2s+1))`. A clock word of all `true` digits one longer than the exponent has
value `2^W - 1 > configBound M n s`. [AB09, §4.1.1, Claim 4.4]

**Proof sketch.** Multiply the four factor bounds and collect the powers of two. -/
theorem FinTM.configBound_le_two_pow (M : FinTM Bool) (n s : ℕ) :
    M.configBound n s ≤
      2 ^ (Fintype.card M.State + posWidth n + 3 * M.k * (2 * s + 1)) := by
  have hQ : Fintype.card M.State + 1 ≤ 2 ^ Fintype.card M.State :=
    Nat.lt_two_pow_self
  have hn : n + 2 ≤ 2 ^ posWidth n := by
    have h := Nat.lt_size_self (n + 1)
    rw [← Nat.size_eq_bits_len] at h
    exact h
  have h3 : 3 ^ (M.k * (2 * s + 1)) ≤ 2 ^ (2 * (M.k * (2 * s + 1))) :=
    calc 3 ^ (M.k * (2 * s + 1)) ≤ 4 ^ (M.k * (2 * s + 1)) :=
          Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * (M.k * (2 * s + 1))) := by
          rw [pow_mul 2 2 (M.k * (2 * s + 1))]
          norm_num
  have hw : (2 * s + 1) ^ M.k ≤ 2 ^ (M.k * (2 * s + 1)) := by
    rw [mul_comm M.k, pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have hsplit : 2 ^ (Fintype.card M.State + posWidth n + 3 * M.k * (2 * s + 1)) =
      2 ^ Fintype.card M.State * 2 ^ posWidth n * 2 ^ (2 * (M.k * (2 * s + 1))) *
        2 ^ (M.k * (2 * s + 1)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hsplit]
  unfold FinTM.configBound
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hQ hn) h3) hw

/-! ### The runner -/

/-- An all-true binary clock has value one less than the corresponding power of two.
**Proof sketch.** Induct on the width, using the binary digit recurrence. -/
private lemma cw_true_value (W : ℕ) :
    Nat.ofDigits 2 ((List.replicate W true).map Bool.toNat) = 2 ^ W - 1 := by
  induction W with
  | zero => simp
  | succ W ih =>
    simp only [List.replicate_succ, List.map_cons, Nat.ofDigits_cons, Bool.toNat_true, ih,
      pow_succ]
    have hp : 0 < 2 ^ W := Nat.pow_pos (by decide)
    omega

/-- The runner's per-round cost is at most a power of two when the position width
fits in the record length. **Proof sketch.** Bound each summand by `2 ^ L`. -/
private lemma cw_round_cost {L n p : ℕ} (hp : p ≤ L) (hn : n + 2 ≤ 2 ^ p) :
    L + n + 1 ≤ 2 ^ (L + 1) := by
  have hpow : 2 ^ p ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hp
  have hL : L < 2 ^ L := Nat.lt_two_pow_self
  rw [pow_succ]
  omega

/-- A constant number of passes over field cells supplies every certified round,
including the extra halt-test round. The layout identities are explicit hypotheses.
**Proof sketch.** Bound the runner cost, configuration count plus one and runner
constant by powers of two. Their combined exponent is strictly below the clock width. -/
private lemma cw_budget {q k n s p L B : ℕ} (C : ℕ)
    (hL : L = k * (2 * s + 1) + p + k + 4) (hn : n + 2 ≤ 2 ^ p)
    (hB : B ≤ 2 ^ (q + p + 3 * k * (2 * s + 1))) :
    C * (B + 1) * (L + n + 1) ≤
      2 ^ ((C + q + 8) * (k * (2 * s + 1) + p + 2)) - 1 := by
  let F := k * (2 * s + 1) + p + 2
  let A := q + p + 3 * k * (2 * s + 1)
  have hk : k ≤ k * (2 * s + 1) := by nlinarith
  have hF : 2 ≤ F := by dsimp [F]; omega
  have hLF : L ≤ 2 * F := by dsimp [F]; omega
  have hA : A ≤ q + 3 * F := by dsimp [A, F]; nlinarith
  have hcost := cw_round_cost (show p ≤ L by omega) hn
  have hC : C ≤ 2 ^ C := (Nat.lt_two_pow_self).le
  have hBp : B + 1 ≤ 2 ^ (A + 1) := by
    have hpos : 0 < 2 ^ A := Nat.pow_pos (by decide)
    rw [pow_succ]
    change B ≤ 2 ^ A at hB
    omega
  have hprod : C * (B + 1) * (L + n + 1) ≤ 2 ^ (C + (A + 1) + (L + 1)) := by
    rw [pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul hC hBp) hcost
  have hexp : C + (A + 1) + (L + 1) < (C + q + 8) * F := by nlinarith
  have hstrict : 2 ^ (C + (A + 1) + (L + 1)) < 2 ^ ((C + q + 8) * F) :=
    Nat.pow_lt_pow_right (by decide) hexp
  exact Nat.le_sub_one_of_lt (lt_of_le_of_lt hprod hstrict)

/-- Linear writer and cleanup costs fit the target's single exponential envelope.
**Proof sketch.** The same power bounds `2 ^ W`, `L + 1` and one; multiply
these three bounds by their nonnegative coefficients and add. -/
private lemma cw_time_bound {c L W : ℕ} (A D : ℕ) (hW : W ≤ c * L) :
    A * (L + 1) + (5 * (2 ^ W - 1) + 2 * W + 3) + (2 * W + 2) + D ≤
      (A + 4 * c + D + 10) * 2 ^ ((A + 4 * c + D + 10) * (L + 1)) := by
  let C := A + 4 * c + D + 10
  let P := 2 ^ (C * (L + 1))
  have hC : 1 ≤ C ∧ c ≤ C := by dsimp [C]; omega
  have hLp : L + 1 ≤ P := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by decide) (show L + 1 ≤ C * (L + 1) by nlinarith))
  have hWp : 2 ^ W ≤ P := Nat.pow_le_pow_right (by decide)
    (show W ≤ C * (L + 1) by nlinarith)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by decide)
  have hwrite := Nat.mul_le_mul_left A hLp
  have hlinear := Nat.mul_le_mul_left (4 * c) hLp
  have hdispatch := Nat.mul_le_mul_left (D + 5) hP
  have hsub : 2 ^ W - 1 ≤ 2 ^ W := Nat.sub_le _ _
  change _ ≤ C * P
  dsimp [C]
  nlinarith

/-- A clock of linear width preserves the runner's linear head envelope. -/
private lemma cw_head_bound {c L W : ℕ} (C : ℕ) (hW : W ≤ c * L) :
    C * (L + W + 1) ≤ C * (c + 1) * (L + 1) := by
  calc
    C * (L + W + 1) ≤ C * ((c + 1) * (L + 1)) :=
      Nat.mul_le_mul_left C (by nlinarith)
    _ = C * (c + 1) * (L + 1) := by ring

/-- The field cells of a configuration record exclude its `k + 2` separators.
**Proof sketch.** Subtract the separator count from the published layout length. -/
private lemma cw_field_total {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ)
    (d : Cfg k Bool Q x) (τ : T) :
    ((cfgRecord s d τ).map List.length).sum = k * (2 * s + 1) + posWidth x.length + 2 := by
  have hcount := cfgRecord_length s d τ
  have hne : cfgRecord s d τ ≠ [] := by
    intro h
    rw [h, List.length_nil] at hcount
    omega
  have hlen := joinFields_length (cfgRecord s d τ) hne
  rw [joinFields_cfgRecord_length, recordLength_eq, hcount] at hlen
  omega

/-- The chosen all-true word fits linearly in the record and supplies the runner's
budget for every round up to the configuration count plus one.
**Proof sketch.** Apply the arithmetic budget to the public record-length and
position-width equations, then use the exact all-true clock value. -/
private lemma cw_record_clock (M : FinTM Bool) {T : Type} {x : List Bool} (s : ℕ)
    (d : Cfg M.k Bool M.State x) (τ : T) (C : ℕ) :
    let c := C + Fintype.card M.State + 8
    let W := c * ((cfgRecord s d τ).map List.length).sum
    W ≤ c * recordLength M.k x.length s ∧
      ∀ N ≤ M.configBound x.length s + 1,
        C * N * (recordLength M.k x.length s + x.length + 1) ≤
          Nat.ofDigits 2 ((List.replicate W true).map Bool.toNat) := by
  dsimp only
  rw [cw_field_total]
  constructor
  · apply Nat.mul_le_mul_left
    rw [recordLength_eq]
    omega
  · intro N hN
    rw [cw_true_value]
    have hn : x.length + 2 ≤ 2 ^ posWidth x.length := record_pos_lt x.length
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hN)).trans
      (cw_budget C (recordLength_eq M.k x.length s) hn
        (M.configBound_le_two_pow x.length s))

/-- The writer's one-step leaf moves the clock head left onto its delimiter.
The catalog skips past a delimiter; no catalog row stops on that delimiter. -/
private def cw_leftTM {Γ : Type} (k : ℕ) (i : Fin k) : MultiTapeTM k Γ Bool where
  q₀ := false
  tr := fun _ _ _ => tapeAction i 0 none .neg true

/-- The delimiter move takes one silent step, keeps the native input position,
and changes only the selected head and control state. -/
private lemma cw_left_run {Γ : Type} {k : ℕ} {x : List Γ} (i : Fin k)
    (d : Cfg k Γ Bool x) (hd : d.state = some false) :
    (cw_leftTM k i).runFrom d 1 =
      { d with state := some true
               workTapePos := Function.update d.workTapePos i (d.workTapePos i - 1) } ∧
      (∀ u < 1, ((cw_leftTM k i).runFrom d u).state ≠ some true) := by
  constructor
  · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have h := step_of_tapeAction_move (cw_leftTM k i) d i 0 .neg hd rfl
    simpa only [moveInputPos_zero, SignType.coe_neg_one, sub_eq_add_neg] using h
  · intro u hu
    have hu0 : u = 0 := by omega
    rw [hu0, MultiTapeTM.runFrom_zero, hd]
    decide

/-- A constant patch reads the constant inside its interval and the original tape outside.
**Proof sketch.** Inside the interval the patch reads the word at a valid offset; outside it
reads the original tape. -/
private lemma cw_patch_rep {Γ : Type} (ct : ℤ → Option Γ) (p : ℤ) (n : ℕ) (e : Γ) (z : ℤ) :
    wordPatch ct p (List.replicate n e) z = if p ≤ z ∧ z < p + n then some e else ct z := by
  by_cases h : p ≤ z ∧ z < p + n
  · rw [if_pos h, wordPatch_of_mem _ _ _ h.1 (by rw [List.length_replicate]; exact h.2),
      ← Int.toNat_of_nonneg (show 0 ≤ z - p by omega), FinTM.bufferTape_nat,
      List.getElem?_replicate, if_pos (by omega)]
  · rw [if_neg h, wordPatch_of_not_mem _ _ _ (by rw [List.length_replicate]; exact h)]

/-- The buffer of a constant word. -/
private lemma cw_buffer_rep {Γ : Type} (n : ℕ) (e : Γ) (z : ℤ) :
    FinTM.bufferTape (List.replicate n e) z = if 0 ≤ z ∧ z < n then some e else none := by
  by_cases h : 0 ≤ z
  · rw [← Int.toNat_of_nonneg h, FinTM.bufferTape_nat, List.getElem?_replicate]
    by_cases hn : z.toNat < n
    · rw [if_pos hn, if_pos (by omega)]
    · rw [if_neg hn, if_neg (by omega)]
  · rw [FinTM.bufferTape_of_neg _ (by omega), if_neg (by omega)]

/-- Two adjacent constant patches are one: the join of a pass's writes. -/
private lemma cw_join {Γ : Type} (ct : ℤ → Option Γ) (p : ℤ) (e : Γ) (n l : ℕ) :
    wordPatch (wordPatch ct p (List.replicate n e)) (p + n) (List.replicate l e) =
      wordPatch ct p (List.replicate (n + l) e) := by
  have h := wordPatch_append ct p (List.replicate n e) (List.replicate l e)
  rw [List.length_replicate, ← List.replicate_add] at h
  exact h

/-- A mapped copy of one field writes a constant symbol on the destination: the destination
tape becomes the patch of `|w|` copies of `e` at its head. It requires delimiters only on the
source, so it also appends to an existing clock prefix. Up to the exit the source and
destination heads stay within one cell of their intervals, and the other heads are fixed.
**Proof sketch.** Use the framed mapped copy. Every cell inside its write interval has a valid
source index, and the constant merge ignores the old destination value. -/
private lemma cw_copy_constant {Γ : Type} {k : ℕ} {x : List Γ}
    (src dst : Fin k) (hne : src ≠ dst) (e : Γ) (w : List Γ)
    (d : Cfg k Γ SweepPhase x) (hd : d.state = some .sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (copyMapTM k src dst (fun _ => ()) (fun _ _ => e)).runFrom d (2 * w.length + 2) =
      { d with state := some .done
               workTapes := fun j q => if j = dst then
                 wordPatch (d.workTapes j) (d.workTapePos j) (List.replicate w.length e) q
                 else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((copyMapTM k src dst (fun _ => ()) (fun _ _ => e)).runFrom d t).state ≠
          some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((copyMapTM k src dst (fun _ => ()) (fun _ _ => e)).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((copyMapTM k src dst (fun _ => ()) (fun _ _ => e)).runFrom d t).workTapePos j =
          d.workTapePos j) := by
  obtain ⟨h₁, h₂, h₃⟩ := copyMapTM_run_ofCfg src dst hne (fun _ => ()) (fun _ _ => e) w d hd hw
  refine ⟨?_, h₂, h₃⟩
  rw [h₁]
  congr 1
  funext j q
  by_cases hj : j = dst
  · rw [if_pos hj, cw_patch_rep]
    by_cases hq : d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
    · rw [if_pos ⟨hj, hq⟩, if_pos hq]
      have hk : (q - d.workTapePos j).toNat < w.length := by omega
      rw [← Int.toNat_of_nonneg (show 0 ≤ q - d.workTapePos j by omega), FinTM.bufferTape_nat,
        List.getElem?_eq_getElem hk]
      rfl
    · rw [if_neg (fun h => hq h.2), if_neg hq]
  · rw [if_neg (fun h => hj h.1), if_neg hj]

/-- Clearing a word patch leaves its tape completely blank when the underlying tape
is blank outside the patch interval. Every other tape, all heads, the native input
position, and the output are preserved. Up to the exit the head stays within one cell of the
interval, and the other heads are fixed.
**Proof sketch.** The patch supplies the clear row's delimited word. The row clears
its interval; outside it, the patch preserves the assumed blank frame. -/
private lemma cw_clear_patch {Γ : Type} {k : ℕ} {x : List Γ} (i : Fin k)
    (w : List Γ) (d : Cfg k Γ SweepPhase x)
    (hb : ∀ q, q < d.workTapePos i ∨ d.workTapePos i + (w.length : ℤ) ≤ q →
      d.workTapes i q = none) :
    let a : Cfg k Γ SweepPhase x :=
      { d with state := some .sweep
               workTapes := fun j q => if j = i then
                 wordPatch (d.workTapes j) (d.workTapePos j) w q else d.workTapes j q }
    (clearTM k i).runFrom a (2 * w.length + 2) =
      { d with state := some .done
               workTapes := fun j q => if j = i then none else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ((clearTM k i).runFrom a t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then ((clearTM k i).runFrom a t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((clearTM k i).runFrom a t).workTapePos j = d.workTapePos j) := by
  dsimp only
  let a : Cfg k Γ SweepPhase x :=
    { d with state := some .sweep
             workTapes := fun j q => if j = i then
               wordPatch (d.workTapes j) (d.workTapePos j) w q else d.workTapes j q }
  change (clearTM k i).runFrom a (2 * w.length + 2) = _ ∧
    (∀ t < 2 * w.length + 2, ((clearTM k i).runFrom a t).state ≠ some .done) ∧
    (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
      if j = i then ((clearTM k i).runFrom a t).workTapePos j ∈
          Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
      else ((clearTM k i).runFrom a t).workTapePos j = d.workTapePos j)
  have hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      a.workTapes i (a.workTapePos i + p) = FinTM.bufferTape w p := by
    intro p hp hlen
    dsimp only [a]
    rw [if_pos rfl]
    by_cases hin : 0 ≤ p ∧ p < (w.length : ℤ)
    · rw [wordPatch_of_mem _ _ _ (by omega) (by omega)]
      congr 1
      omega
    · rw [wordPatch_of_not_mem _ _ _ (by omega), hb _ (by omega)]
      rcases (show p = -1 ∨ p = (w.length : ℤ) by omega) with rfl | rfl
      · rw [FinTM.bufferTape_left]
      · rw [FinTM.bufferTape_nat, List.getElem?_length]
  obtain ⟨h₁, h₂, h₃⟩ := clearTM_run_ofCfg i w a rfl hw
  refine ⟨?_, h₂, h₃⟩
  rw [h₁]
  apply Cfg.ext <;> try rfl
  funext j q
  dsimp only [a]
  by_cases hj : j = i
  · subst j
    simp only [ite_true, true_and]
    by_cases hq : d.workTapePos i ≤ q ∧ q < d.workTapePos i + (w.length : ℤ)
    · rw [if_pos hq]
    · rw [if_neg hq, wordPatch_of_not_mem _ _ _ hq, hb q (by omega)]
  · simp only [hj, false_and, ite_false]

/-! #### The clock writer and the runner on one phase host

The clock word is written field by field. In each of `c` passes, every field of the record is
copied onto the clock tape through the constant map, the record head skips to the next field,
the clock head skips past the written cells and steps back onto the clock's right delimiter,
where the next copy continues the word. Between passes the record head skips back over the
fields. All phases, the windowed runner, the clear of the clock and the exits run on one phase
host. -/

/-- The host's phases. In pass `p`, field `j` takes four phases: the constant copy onto the
clock, the skip past the field on the record tape, the skip past the written cells on the
clock, and the one-cell move back onto the clock's delimiter. After a pass the record head
skips back field by field. After the last pass the clock head returns to the clock's first
cell in two phases; then come the windowed runner, the clear of the clock after a `halted` or
`left` exit, and the exits. -/
private inductive cw_Idx (c m : ℕ) where
  /-- the constant copy of field `j` onto the clock, in pass `p` -/
  | copy (p : Fin c) (j : Fin m)
  /-- the skip past field `j` on the record tape -/
  | skipS (p : Fin c) (j : Fin m)
  /-- the skip past the written cells on the clock, after field `j` of pass `p`, or after the
  last pass (`none`) the step past the clock's right delimiter -/
  | skipC (o : Option (Fin c × Fin m))
  /-- the one-cell move back onto the clock's right delimiter -/
  | left (p : Fin c) (j : Fin m)
  /-- the skip back over field `j` on the record tape -/
  | back (p : Fin c) (j : Fin m)
  /-- the skip back over the clock word -/
  | clockBack
  /-- the windowed runner -/
  | run
  /-- the clear of the clock after a `halted` (`true`) or `left` (`false`) exit -/
  | clear (b : Bool)
  /-- the stationary exits -/
  | stop
  deriving DecidableEq, Fintype

/-- Each phase's controls: its row's, the runner's, and the exits. -/
private def cw_Ctrl (P : Type) {c m : ℕ} : cw_Idx c m → Type
  | .copy _ _ => SweepPhase
  | .skipS _ _ => SeekPhase
  | .skipC _ => SeekPhase
  | .left _ _ => Bool
  | .back _ _ => SeekPhase
  | .clockBack => SeekPhase
  | .run => P
  | .clear _ => SweepPhase
  | .stop => WindowExit

/-- The controls are finite. The three exits are listed here, since `Turing.WindowExit` has
no public `Fintype` instance. -/
private instance cw_Ctrl_fintype (P : Type) [Fintype P] {c m : ℕ} (i : cw_Idx c m) :
    Fintype (cw_Ctrl P i) := by
  cases i <;> dsimp only [cw_Ctrl] <;> first
    | infer_instance
    | exact ⟨{.halted, .left, .exhausted}, fun y => by cases y <;> simp⟩

/-- The controls have decidable equality. -/
private instance cw_Ctrl_decidableEq (P : Type) [DecidableEq P] {c m : ℕ} (i : cw_Idx c m) :
    DecidableEq (cw_Ctrl P i) := by
  cases i <;> dsimp only [cw_Ctrl] <;> infer_instance

/-- The phase machines: the writer's rows on the record tape `0` and the clock tape
`Fin.last (K + 1)`, the windowed runner `R`, the clear, and stationary exits. -/
private def cw_rows {K : ℕ} {Γ P : Type} (e : Γ) (R : MultiTapeTM (K + 2) Γ P) {c m : ℕ} :
    (i : cw_Idx c m) → MultiTapeTM (K + 2) Γ (cw_Ctrl P i)
  | .copy _ _ => copyMapTM (K + 2) 0 (Fin.last (K + 1)) (fun _ => ()) (fun _ _ => e)
  | .skipS _ _ => skipTM (K + 2) 0
  | .skipC _ => skipTM (K + 2) (Fin.last (K + 1))
  | .left _ _ => cw_leftTM (K + 2) (Fin.last (K + 1))
  | .back _ _ => skipBackTM (K + 2) 0
  | .clockBack => skipBackTM (K + 2) (Fin.last (K + 1))
  | .run => R
  | .clear _ => clearTM (K + 2) (Fin.last (K + 1))
  | .stop => ⟨WindowExit.exhausted, fun q _ _ => ⟨0, fun _ => (none, 0), none, some q⟩⟩

/-- The phase after field `j`'s round: the next field's copy, or after the last field the
record's rewind. -/
private def cw_next {P : Type} {c m : ℕ} (p : Fin c) (j : Fin m) :
    Σ i : cw_Idx c m, cw_Ctrl P i :=
  if h : j.val + 1 < m then ⟨.copy p ⟨j.val + 1, h⟩, (SweepPhase.sweep : SweepPhase)⟩
  else ⟨.back p j, (SeekPhase.run : SeekPhase)⟩

/-- The phase after the skip back over field `j`: the skip back over the previous field, or
after the first field the next pass, or after the last pass the clock's rewind. -/
private def cw_prev {P : Type} {c m : ℕ} (p : Fin c) (j : Fin m) :
    Σ i : cw_Idx c m, cw_Ctrl P i :=
  if 0 < j.val then
    ⟨.back p ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩, (SeekPhase.run : SeekPhase)⟩
  else if h : p.val + 1 < c then
    ⟨.copy ⟨p.val + 1, h⟩ ⟨0, j.pos⟩, (SweepPhase.sweep : SweepPhase)⟩
  else ⟨.skipC none, (SeekPhase.run : SeekPhase)⟩

/-- The phase after the skip on the clock: the move back onto the clock's delimiter after a
field, or the skip back over the clock word after the last pass. -/
private def cw_afterSkip {P : Type} {c m : ℕ} :
    Option (Fin c × Fin m) → Σ i : cw_Idx c m, cw_Ctrl P i
  | some (p, j) => ⟨.left p j, false⟩
  | none => ⟨.clockBack, (SeekPhase.run : SeekPhase)⟩

/-- The redirect table. The writer's phases follow one another at their rows' `done` anchors
(the one-cell move at `true`); the runner's `halted` and `left` exits enter the clear and its
`exhausted` exit stops; the clear stops with the runner's exit. -/
private def cw_red {P : Type} [DecidableEq P] (en : P) (ex : WindowExit → P) {c m : ℕ} :
    (i : cw_Idx c m) → cw_Ctrl P i → Option (Σ i : cw_Idx c m, cw_Ctrl P i)
  | .copy p j, q =>
    if q = SweepPhase.done then some ⟨.skipS p j, (SeekPhase.run : SeekPhase)⟩ else none
  | .skipS p j, q =>
    if q = SeekPhase.done then some ⟨.skipC (some (p, j)), (SeekPhase.run : SeekPhase)⟩ else none
  | .skipC o, q => if q = SeekPhase.done then some (cw_afterSkip o) else none
  | .left p j, q => if q = true then some (cw_next p j) else none
  | .back p j, q => if q = SeekPhase.done then some (cw_prev p j) else none
  | .clockBack, q => if q = SeekPhase.done then some ⟨.run, en⟩ else none
  | .run, q =>
    if q = ex .halted then some ⟨.clear true, (SweepPhase.sweep : SweepPhase)⟩
    else if q = ex .left then some ⟨.clear false, (SweepPhase.sweep : SweepPhase)⟩
    else if q = ex .exhausted then some ⟨.stop, (WindowExit.exhausted : WindowExit)⟩
    else none
  | .clear b, q =>
    if q = SweepPhase.done then
      some ⟨.stop, (if b then .halted else .left : WindowExit)⟩
    else none
  | .stop, _ => none

/-- The configuration-count runner's machine: the phase host over `cw_rows` and `cw_red`. Its
initial control is never used: the runner is started at the first copy's control. -/
private def cw_hostTM {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) (c m : ℕ) :
    MultiTapeTM (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) :=
  phaseHostTM (cw_rows e R) ⟨.stop, (WindowExit.exhausted : WindowExit)⟩ (cw_red en ex)

/-- The writer's configurations: the start configuration `d` with control `q`, the record
head moved by `a`, the clock head by `b`, and `n` copies of `e` patched onto the clock tape at
the clock's start. -/
private def cw_cfg {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ) (d : Cfg (K + 2) Γ P x)
    (q : S) (a : ℤ) (n : ℕ) (b : ℤ) : Cfg (K + 2) Γ S x :=
  ⟨some q, d.inputPos,
    fun j z => if j = Fin.last (K + 1) then
      wordPatch (d.workTapes j) (d.workTapePos j) (List.replicate n e) z else d.workTapes j z,
    fun j => if j = 0 then d.workTapePos j + a
      else if j = Fin.last (K + 1) then d.workTapePos j + b else d.workTapePos j,
    d.output⟩

/-- The record tape and the clock tape are distinct. -/
private lemma cw_zero_ne_last (K : ℕ) : (0 : Fin (K + 2)) ≠ Fin.last (K + 1) := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h'
  omega


/-- The clock tape of a writer configuration is the constant patch. -/
private lemma cw_cfg_clockTape {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) :
    (cw_cfg e d q a n b).workTapes (Fin.last (K + 1)) =
      wordPatch (d.workTapes (Fin.last (K + 1))) (d.workTapePos (Fin.last (K + 1)))
        (List.replicate n e) :=
  funext fun _ => if_pos rfl

/-- A clock cell of a writer configuration. -/
private lemma cw_cfg_clock {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) (z : ℤ) :
    (cw_cfg e d q a n b).workTapes (Fin.last (K + 1)) z =
      if d.workTapePos (Fin.last (K + 1)) ≤ z ∧ z < d.workTapePos (Fin.last (K + 1)) + n
        then some e else d.workTapes (Fin.last (K + 1)) z := by
  rw [cw_cfg_clockTape, cw_patch_rep]

/-- The other tapes of a writer configuration are the start configuration's. -/
private lemma cw_cfg_tape {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) (j : Fin (K + 2))
    (hj : j ≠ Fin.last (K + 1)) (z : ℤ) :
    (cw_cfg e d q a n b).workTapes j z = d.workTapes j z :=
  if_neg hj

/-- The record head of a writer configuration. -/
private lemma cw_cfg_pos₀ {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) :
    (cw_cfg e d q a n b).workTapePos 0 = d.workTapePos 0 + a := by
  dsimp only [cw_cfg]
  rw [if_pos rfl]

/-- The clock head of a writer configuration. -/
private lemma cw_cfg_posL {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) :
    (cw_cfg e d q a n b).workTapePos (Fin.last (K + 1)) =
      d.workTapePos (Fin.last (K + 1)) + b := by
  dsimp only [cw_cfg]
  rw [if_neg (cw_zero_ne_last K).symm, if_pos rfl]

/-- The other heads of a writer configuration are the start configuration's. -/
private lemma cw_cfg_pos {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) (j : Fin (K + 2)) (h₀ : j ≠ 0)
    (hL : j ≠ Fin.last (K + 1)) :
    (cw_cfg e d q a n b).workTapePos j = d.workTapePos j := by
  dsimp only [cw_cfg]
  rw [if_neg h₀, if_neg hL]

/-- Renaming the control keeps the heads. -/
private lemma cw_mapState_pos {k : ℕ} {Γ S S' : Type} {x : List Γ} (f : S → S')
    (a : Cfg k Γ S x) : (a.mapState f).workTapePos = a.workTapePos :=
  funext (Cfg.mapState_workTapePos f a)

/-- Renaming the control keeps the tapes. -/
private lemma cw_mapState_tapes {k : ℕ} {Γ S S' : Type} {x : List Γ} (f : S → S')
    (a : Cfg k Γ S x) : (a.mapState f).workTapes = a.workTapes :=
  funext fun j => funext (Cfg.mapState_workTapes f a j)

/-- Renaming the control keeps the input position and the output. -/
private lemma cw_mapState_io {k : ℕ} {Γ S S' : Type} {x : List Γ} (f : S → S')
    (a : Cfg k Γ S x) : (a.mapState f).inputPos = a.inputPos ∧ (a.mapState f).output = a.output :=
  ⟨Cfg.mapState_inputPos f a, Cfg.mapState_output f a⟩

/-- Renaming the control of a writer configuration. -/
private lemma cw_cfg_mapState {K : ℕ} {Γ P S S' : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (a : ℤ) (n : ℕ) (b : ℤ) (f : S → S') :
    (cw_cfg e d q a n b).mapState f = cw_cfg e d (f q) a n b := by
  refine Cfg.ext ?_ (cw_mapState_io f _).1 (cw_mapState_tapes f _) (cw_mapState_pos f _)
    (cw_mapState_io f _).2
  rw [Cfg.mapState_state]
  rfl

/-- A writer configuration with both heads at the start has the start's heads. -/
private lemma cw_cfg_pos_zero {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q : S) (n : ℕ) :
    (cw_cfg e d q 0 n 0).workTapePos = d.workTapePos := by
  funext j
  by_cases h₀ : j = 0
  · subst h₀
    rw [cw_cfg_pos₀, add_zero]
  · by_cases hL : j = Fin.last (K + 1)
    · subst hL
      rw [cw_cfg_posL, add_zero]
    · exact cw_cfg_pos e d q 0 n 0 j h₀ hL

/-- With nothing moved or written, a writer configuration is its start configuration. -/
private lemma cw_cfg_zero {K : ℕ} {Γ P : Type} {x : List Γ} (e : Γ) (d : Cfg (K + 2) Γ P x)
    (q : P) (hd : d.state = some q) : cw_cfg e d q 0 0 0 = d := by
  refine Cfg.ext hd.symm rfl ?_ (cw_cfg_pos_zero e d q 0) rfl
  funext j z
  by_cases hj : j = Fin.last (K + 1)
  · subst hj
    rw [cw_cfg_clock, if_neg (by push_cast; omega)]
  · exact cw_cfg_tape e d q 0 0 0 j hj z

/-- Moving the record head of a writer configuration and renaming its control. -/
private lemma cw_cfg_move₀ {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q q' : S) (a : ℤ) (n : ℕ) (b v a' : ℤ)
    (hv : v = d.workTapePos 0 + a') :
    ({ cw_cfg e d q a n b with
        state := some q'
        workTapePos := Function.update (cw_cfg e d q a n b).workTapePos 0 v } :
        Cfg (K + 2) Γ S x) = cw_cfg e d q' a' n b := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  dsimp only
  by_cases h₀ : j = 0
  · subst h₀
    rw [Function.update_self, hv, cw_cfg_pos₀]
  · rw [Function.update_of_ne h₀]
    dsimp only [cw_cfg]
    rw [if_neg h₀, if_neg h₀]

/-- Moving the clock head of a writer configuration and renaming its control. -/
private lemma cw_cfg_moveL {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (q q' : S) (a : ℤ) (n : ℕ) (b v b' : ℤ)
    (hv : v = d.workTapePos (Fin.last (K + 1)) + b') :
    ({ cw_cfg e d q a n b with
        state := some q'
        workTapePos := Function.update (cw_cfg e d q a n b).workTapePos (Fin.last (K + 1)) v } :
        Cfg (K + 2) Γ S x) = cw_cfg e d q' a n b' := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  dsimp only
  by_cases hL : j = Fin.last (K + 1)
  · subst hL
    rw [Function.update_self, hv, cw_cfg_posL]
  · rw [Function.update_of_ne hL]
    by_cases h₀ : j = 0
    · subst h₀
      rw [cw_cfg_pos₀, cw_cfg_pos₀]
    · rw [cw_cfg_pos e d q a n b j h₀ hL, cw_cfg_pos e d q' a n b' j h₀ hL]

/-- Every head within `r` cells of its position in `o`. -/
private def cw_box {k : ℕ} (o : Fin k → ℤ) (r : ℕ) (pos : Fin k → ℤ) : Prop :=
  ∀ j, |pos j - o j| ≤ (r : ℤ)

/-- The box from the record and clock heads' ranges, with every other head fixed. -/
private lemma cw_box_of {K : ℕ} (o pos : Fin (K + 2) → ℤ) (r : ℕ) (lo₀ hi₀ loL hiL : ℤ)
    (h₀ : o 0 + lo₀ ≤ pos 0 ∧ pos 0 ≤ o 0 + hi₀)
    (hL : o (Fin.last (K + 1)) + loL ≤ pos (Fin.last (K + 1)) ∧
      pos (Fin.last (K + 1)) ≤ o (Fin.last (K + 1)) + hiL)
    (ho : ∀ j, j ≠ 0 → j ≠ Fin.last (K + 1) → pos j = o j)
    (hr : -(r : ℤ) ≤ lo₀ ∧ hi₀ ≤ r ∧ -(r : ℤ) ≤ loL ∧ hiL ≤ r) : cw_box o r pos := by
  intro j
  rw [abs_le]
  by_cases hj₀ : j = 0
  · subst hj₀
    omega
  · by_cases hjL : j = Fin.last (K + 1)
    · subst hjL
      omega
    · rw [ho j hj₀ hjL]
      omega

/-- The box from one row's head range: the head of tape `i` within `[lo i, hi i]` and every
other head at its start, where it lies in the box. -/
private lemma cw_box_row {k : ℕ} (o start pos lo hi : Fin k → ℤ) (r : ℕ) (i : Fin k)
    (h : ∀ j, if j = i then pos j ∈ Finset.Icc (lo j) (hi j) else pos j = start j)
    (hrange : o i - r ≤ lo i ∧ hi i ≤ o i + r)
    (hstart : ∀ j, |start j - o j| ≤ (r : ℤ)) : cw_box o r pos := by
  intro j
  have hj := h j
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, Finset.mem_Icc] at hj
    rw [abs_le]
    omega
  · rw [if_neg hji] at hj
    rw [hj]
    exact hstart j

/-- A writer configuration whose heads are moved by at most `r` lies in the box. -/
private lemma cw_cfg_box {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ) (d : Cfg (K + 2) Γ P x)
    (q : S) (a : ℤ) (n : ℕ) (b : ℤ) (r : ℕ) (ha : |a| ≤ r) (hb : |b| ≤ r) :
    cw_box d.workTapePos r (cw_cfg e d q a n b).workTapePos := by
  intro j
  by_cases h₀ : j = 0
  · subst h₀
    rw [cw_cfg_pos₀, add_sub_cancel_left]
    exact ha
  · by_cases hL : j = Fin.last (K + 1)
    · subst hL
      rw [cw_cfg_posL, add_sub_cancel_left]
      exact hb
    · rw [cw_cfg_pos e d q a n b j h₀ hL, sub_self, abs_zero]
      positivity

/-- A phase redirected only at `v`, which its row avoids before `t`, is never redirected
before `t`. -/
private lemma cw_guard {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ} (i : cw_Idx c m)
    {x : List Γ} (a : Cfg (K + 2) Γ (cw_Ctrl P i) x) (t : ℕ) (v : cw_Ctrl P i)
    (hcut : ∀ u < t, ((cw_rows e R i).runFrom a u).state ≠ some v)
    (hnone : ∀ z, z ≠ v → cw_red en ex i z = none) :
    ∀ u < t, ∀ z, ((cw_rows e R i).runFrom a u).state = some z → cw_red en ex i z = none :=
  fun u hu z hz => hnone z fun h => hcut u hu (h ▸ hz)

/-- **One phase as a host segment.** A phase other than the exits, run from `a` to `b` and
dispatched by the redirect table, is a segment of the host that avoids the exits, and its head
relation holds through the dispatch.
**Proof sketch.** The phase lemma of the phase host gives the tagged prefix and the dispatch;
a tagged control is never an exit's, and the dispatch keeps the heads. -/
private lemma cw_seg {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ}
    (i : cw_Idx c m) (hi : i ≠ .stop) {x : List Γ} (a b : Cfg (K + 2) Γ (cw_Ctrl P i) x)
    (t : ℕ) (h : (cw_rows e R i).runFrom a t = b) (v : cw_Ctrl P i) (hv : b.state = some v)
    (q : Σ i : cw_Idx c m, cw_Ctrl P i) (hred : cw_red en ex i v = some q)
    (hguard : ∀ u < t, ∀ z, ((cw_rows e R i).runFrom a u).state = some z →
      cw_red en ex i z = none)
    (B : (Fin (K + 2) → ℤ) → Prop)
    (hB : ∀ u ≤ t, B ((cw_rows e R i).runFrom a u).workTapePos) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩} B
      (a.mapState (Sigma.mk i)) (b.mapState fun _ => q) (t + 1) := by
  obtain ⟨hpre, hend⟩ :=
    phaseHostTM_run (cw_rows e R) _ (cw_red en ex) i a b t h v hv q hred hguard
  unfold cw_hostTM
  refine (segment_iff _ _ _ _ _ _).2 ⟨hend, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hpre u (by omega), Cfg.mapState_state]
    rintro ⟨y, hy⟩
    obtain ⟨z, -, hz⟩ := Option.map_eq_some_iff.mp hy
    exact hi (congrArg Sigma.fst hz)
  · rcases Nat.lt_or_ge u (t + 1) with hu' | hu'
    · rw [hpre u (by omega), cw_mapState_pos]
      exact hB u (by omega)
    · obtain rfl : u = t + 1 := by omega
      rw [hend, cw_mapState_pos, ← h]
      exact hB t le_rfl

/-- **A row moving one head**, as a host segment. The row of phase `i` runs from the writer
configuration with control `s` to its anchor `v` in `t` steps, moving only the head of tape
`k₀`, within `[lo k₀, up k₀]`; its endpoint is the writer configuration with offsets `a'` and
`b'`, and the redirect continues at `q`. -/
private lemma cw_seg_row {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ} (i : cw_Idx c m)
    (hi : i ≠ .stop) {x : List Γ} (d : Cfg (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) x)
    (s v : cw_Ctrl P i) (q : Σ i : cw_Idx c m, cw_Ctrl P i)
    (hdone : ∀ z, cw_red en ex i z = if z = v then some q else none)
    (a a' : ℤ) (n : ℕ) (b b' : ℤ) (t r : ℕ) (k₀ : Fin (K + 2)) (w : ℤ)
    (lo up : Fin (K + 2) → ℤ)
    (h₁ : (cw_rows e R i).runFrom (cw_cfg e d s a n b) t =
      { cw_cfg e d s a n b with
        state := some v
        workTapePos := Function.update (cw_cfg e d s a n b).workTapePos k₀ w })
    (hend : ({ cw_cfg e d s a n b with
        state := some v
        workTapePos := Function.update (cw_cfg e d s a n b).workTapePos k₀ w } :
        Cfg (K + 2) Γ (cw_Ctrl P i) x) = cw_cfg e d v a' n b')
    (h₂ : ∀ u < t, ((cw_rows e R i).runFrom (cw_cfg e d s a n b) u).state ≠ some v)
    (h₃ : ∀ (j : Fin (K + 2)) (u : ℕ), u ≤ t →
      if j = k₀ then ((cw_rows e R i).runFrom (cw_cfg e d s a n b) u).workTapePos j ∈
          Finset.Icc (lo j) (up j)
      else ((cw_rows e R i).runFrom (cw_cfg e d s a n b) u).workTapePos j =
        (cw_cfg e d s a n b).workTapePos j)
    (hrange : d.workTapePos k₀ - r ≤ lo k₀ ∧ up k₀ ≤ d.workTapePos k₀ + r)
    (ha : |a| ≤ r) (hb : |b| ≤ r) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩}
      (cw_box d.workTapePos r) (cw_cfg e d (⟨i, s⟩ : Σ i, cw_Ctrl P i) a n b)
      (cw_cfg e d q a' n b') (t + 1) := by
  have hseg := cw_seg e R en ex i hi _ _ t (h₁.trans hend) v rfl q (by rw [hdone, if_pos rfl])
    (cw_guard e R en ex i _ t v h₂ fun z hz => by rw [hdone, if_neg hz]) (cw_box d.workTapePos r)
    (fun u hu => cw_box_row _ _ _ _ _ r k₀ (fun j => h₃ j u hu) hrange
      (cw_cfg_box e d s a n b r ha hb))
  simp only [cw_cfg_mapState] at hseg
  exact hseg


/-- **The copy of a field onto the clock**, as a host segment: the clock gains `|f|` cells of
`e` at its head, which stays. The field `f` lies at the record head moved by `a`.
**Proof sketch.** The constant copy's endpoint patches the clock at its head; joined to the
clock's earlier patch it is the longer patch. -/
private lemma cw_seg_copy {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ} (p : Fin c)
    (j : Fin m) {x : List Γ} (d : Cfg (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) x)
    (f : List Γ) (a : ℤ) (n n' r : ℕ)
    (hf : ∀ z : ℤ, -1 ≤ z → z ≤ (f.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a + z) = FinTM.bufferTape f z)
    (hn' : n' = n + f.length) (ha : 0 ≤ a) (har : a + f.length ≤ r) (hnr : n' + 1 ≤ r) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩}
      (cw_box d.workTapePos r)
      (cw_cfg e d (⟨.copy p j, (SweepPhase.sweep : SweepPhase)⟩ : Σ i, cw_Ctrl P i) a n n)
      (cw_cfg e d (⟨.skipS p j, (SeekPhase.run : SeekPhase)⟩ : Σ i, cw_Ctrl P i) a n' n)
      (2 * f.length + 2 + 1) := by
  subst hn'
  let a₀ : Cfg (K + 2) Γ SweepPhase x := cw_cfg e d SweepPhase.sweep a n n
  have hw : ∀ z : ℤ, -1 ≤ z → z ≤ (f.length : ℤ) →
      a₀.workTapes 0 (a₀.workTapePos 0 + z) = FinTM.bufferTape f z := by
    intro z hz₁ hz₂
    rw [cw_cfg_tape e d _ a n n 0 (cw_zero_ne_last K), cw_cfg_pos₀]
    exact hf z hz₁ hz₂
  obtain ⟨h₁, h₂, h₃⟩ :=
    cw_copy_constant 0 (Fin.last (K + 1)) (cw_zero_ne_last K) e f a₀ rfl hw
  have hend : (copyMapTM (K + 2) 0 (Fin.last (K + 1)) (fun _ => ()) (fun _ _ => e)).runFrom
      a₀ (2 * f.length + 2) = cw_cfg e d SweepPhase.done a (n + f.length) n := by
    rw [h₁]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext j z
    by_cases hj : j = Fin.last (K + 1)
    · subst hj
      show (if Fin.last (K + 1) = Fin.last (K + 1) then _ else _) = _
      rw [if_pos rfl, cw_cfg_clockTape, cw_cfg_clockTape, cw_cfg_posL, cw_join]
    · show (if j = Fin.last (K + 1) then _ else _) = _
      rw [if_neg hj, cw_cfg_tape e d _ a n n j hj, cw_cfg_tape e d _ a (n + f.length) n j hj]
  have hseg := cw_seg e R en ex (.copy p j) (by simp) a₀ _ _ hend SweepPhase.done rfl
    ⟨.skipS p j, (SeekPhase.run : SeekPhase)⟩ (by rw [cw_red, if_pos rfl])
    (cw_guard e R en ex (.copy p j) a₀ _ _ h₂ fun z hz => by rw [cw_red, if_neg hz])
    (cw_box d.workTapePos r) (fun u hu => by
      have hr₀ := h₃ 0 u hu
      have hrL := h₃ (Fin.last (K + 1)) u hu
      rw [if_pos (Or.inl rfl), Finset.mem_Icc, cw_cfg_pos₀] at hr₀
      rw [if_pos (Or.inr rfl), Finset.mem_Icc, cw_cfg_posL] at hrL
      refine cw_box_of _ _ r (a - 1) (a + f.length) (n - 1) (n + f.length)
        (by omega) (by omega) (fun j h₀ hL => ?_) (by omega)
      have hrj := h₃ j u hu
      rw [if_neg (by tauto), cw_cfg_pos e d _ a n n j h₀ hL] at hrj
      exact hrj)
  simp only [a₀, cw_cfg_mapState] at hseg
  exact hseg

/-- **The skip past a field on the record tape**, as a host segment.
**Proof sketch.** The framed skip over the field, whose right delimiter is the record's
separator; nothing else moves. -/
private lemma cw_seg_skipS {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ} (p : Fin c)
    (j : Fin m) {x : List Γ} (d : Cfg (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) x)
    (f : List Γ) (a a' : ℤ) (n : ℕ) (b : ℤ) (r : ℕ)
    (hf : ∀ z : ℤ, 0 ≤ z → z ≤ (f.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a + z) = FinTM.bufferTape f z)
    (ha' : a' = a + f.length + 1) (ha : 0 ≤ a) (har : a' ≤ r) (hbr : |b| ≤ r) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩}
      (cw_box d.workTapePos r)
      (cw_cfg e d (⟨.skipS p j, (SeekPhase.run : SeekPhase)⟩ : Σ i, cw_Ctrl P i) a n b)
      (cw_cfg e d (⟨.skipC (some (p, j)), (SeekPhase.run : SeekPhase)⟩ : Σ i, cw_Ctrl P i) a' n b)
      (f.length + 1 + 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := skipTM_run_ofCfg 0 f (cw_cfg e d SeekPhase.run a n b) rfl
    fun z hz₁ hz₂ => by
      rw [cw_cfg_tape e d _ a n b 0 (cw_zero_ne_last K), cw_cfg_pos₀]
      exact hf z hz₁ hz₂
  exact cw_seg_row e R en ex (.skipS p j) (by simp) d SeekPhase.run SeekPhase.done _
    (fun _ => rfl) a a' n b b _ r 0 _
    _ _ h₁ (cw_cfg_move₀ e d _ _ a n b _ a' (by rw [cw_cfg_pos₀]; omega)) h₂ h₃
    (by rw [cw_cfg_pos₀]; omega) (by rw [abs_of_nonneg ha]; omega) hbr

/-- The written cells after the clock head, then a blank: the word under the clock head; with
the head at the clock's start, the blank before it too.
**Proof sketch.** The cells after the head are inside the constant patch up to its end; the
cells around it were blank before the writer. -/
private lemma cw_skip_word {K : ℕ} {Γ P S : Type} {x : List Γ} (e : Γ)
    (d : Cfg (K + 2) Γ P x) (hclk : ∀ z, d.workTapes (Fin.last (K + 1)) z = none) (q : S)
    (a : ℤ) (N b l : ℕ) (hN : N = b + l) :
    ∀ z : ℤ, 0 ≤ z ∨ b = 0 ∧ -1 ≤ z → z ≤ ((List.replicate l e).length : ℤ) →
      (cw_cfg e d q a N b).workTapes (Fin.last (K + 1))
          ((cw_cfg e d q a N b).workTapePos (Fin.last (K + 1)) + z) =
        FinTM.bufferTape (List.replicate l e) z := by
  intro z hz₁ hz₂
  rw [List.length_replicate] at hz₂
  rw [cw_cfg_clock, cw_cfg_posL, cw_buffer_rep]
  by_cases hz : 0 ≤ z ∧ z < l
  · rw [if_pos (by omega), if_pos hz]
  · rw [if_neg (by omega), if_neg hz, hclk]

/-- **The skip past the written cells on the clock**, as a host segment: the clock head
stops one cell past the clock's right delimiter. After a field (`some (p, j)`) the move back
onto the delimiter follows; after the last pass (`none`, with nothing left to skip) the skip
back over the clock word. -/
private lemma cw_seg_skipC {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ}
    (o : Option (Fin c × Fin m)) {x : List Γ}
    (d : Cfg (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) x)
    (hclk : ∀ z, d.workTapes (Fin.last (K + 1)) z = none) (a : ℤ) (N b l : ℕ) (hN : N = b + l)
    (b' : ℤ) (hb' : b' = b + l + 1) (r : ℕ) (har : |a| ≤ r) (hbr : b' ≤ r) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩}
      (cw_box d.workTapePos r)
      (cw_cfg e d (⟨.skipC o, (SeekPhase.run : SeekPhase)⟩ : Σ i, cw_Ctrl P i) a N b)
      (cw_cfg e d (cw_afterSkip o) a N b') (l + 1 + 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := skipTM_run_ofCfg (Fin.last (K + 1)) _ _ rfl
    fun z h₀ hz => cw_skip_word e d hclk SeekPhase.run a N b l hN z (Or.inl h₀) hz
  rw [List.length_replicate] at h₁ h₂ h₃
  exact cw_seg_row e R en ex (.skipC o) (by simp) d SeekPhase.run SeekPhase.done _
    (fun _ => rfl) a a N b b' _ r _ _ _
    _ h₁ (cw_cfg_moveL e d _ _ a _ b _ b' (by rw [cw_cfg_posL]; omega)) h₂ h₃
    (by rw [cw_cfg_posL]; omega) har (by rw [abs_of_nonneg (by positivity)]; omega)

/-- **The one-cell move back onto the clock's delimiter**, as a host segment, followed by the
next field's copy or, after the last field, the record's rewind. -/
private lemma cw_seg_left {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ} (p : Fin c)
    (j : Fin m) {x : List Γ} (d : Cfg (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) x)
    (a : ℤ) (n : ℕ) (b b' : ℤ) (hb' : b' = b - 1) (r : ℕ) (har : |a| ≤ r) (hb : 1 ≤ b)
    (hbr : b ≤ r) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩}
      (cw_box d.workTapePos r)
      (cw_cfg e d (⟨.left p j, false⟩ : Σ i, cw_Ctrl P i) a n b)
      (cw_cfg e d (cw_next p j) a n b') (1 + 1) := by
  obtain ⟨h₁, h₂⟩ := cw_left_run (Fin.last (K + 1)) (cw_cfg e d false a n b) rfl
  have hend : (cw_leftTM (K + 2) (Fin.last (K + 1))).runFrom (cw_cfg e d false a n b) 1 =
      cw_cfg e d true a n b' :=
    h₁.trans (cw_cfg_moveL e d _ _ a n b _ b' (by rw [cw_cfg_posL]; omega))
  have hseg := cw_seg e R en ex (.left p j) (by simp) _ _ _ hend true rfl (cw_next p j)
    (by rw [cw_red, if_pos rfl])
    (cw_guard e R en ex (.left p j) _ _ _ h₂ fun z hz => by rw [cw_red, if_neg hz])
    (cw_box d.workTapePos r) (fun u hu => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
      · rw [MultiTapeTM.runFrom_zero]
        exact cw_cfg_box e d _ a n b r har (by rw [abs_of_nonneg (by omega)]; exact hbr)
      · rw [hend]
        exact cw_cfg_box e d _ a n b' r har (by rw [abs_of_nonneg (by omega)]; omega))
  simp only [cw_cfg_mapState] at hseg
  exact hseg

/-- A segment's length may be restated. -/
private lemma cw_seg_time {k : ℕ} {Γ S : Type} {x : List Γ} {M : MultiTapeTM k Γ S}
    {F : Set (Option S)} {B : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t t' : ℕ}
    (h : Segment M F B a b t) (ht : t = t') : Segment M F B a b t' :=
  ht ▸ h

/-- Field `i` of a record at the head of tape `r` is a delimited word at its offset. -/
private lemma cw_field {K : ℕ} {Γ S : Type} {x : List Γ} (d : Cfg K Γ S x) (r : Fin K)
    (rs : List (List Γ)) (hrs : RecordAt d r rs) (i : ℕ) (hi : i < rs.length) :
    ∀ z : ℤ, -1 ≤ z → z ≤ (rs[i].length : ℤ) →
      d.workTapes r (d.workTapePos r + fieldOffset rs i + z) = FinTM.bufferTape rs[i] z := by
  intro z hz₁ hz₂
  have hcell := (recordAt_iff d r rs).1 hrs (fieldOffset rs i + z)
    (by omega) (by have := fieldOffset_add_length_le rs i hi; omega)
  rw [← add_assoc] at hcell
  rw [hcell]
  exact fieldsTape_field rs i hi z hz₁ hz₂

/-- **One field's round**: the constant copy of field `j` onto the clock at its head, the skips
past the field on the record tape and past the written cells on the clock, and the move back
onto the clock's delimiter. The clock gains `|fs[j]|` cells of `e`, joined to the earlier ones,
and its head moves past them; the record head moves to the next field; nothing else changes.
**Proof sketch.** Concatenate the four phase segments; the record's field `j` is a delimited
word at its offset. -/
private lemma cw_round {K : ℕ} {Γ P : Type} [DecidableEq P] (e : Γ)
    (R : MultiTapeTM (K + 2) Γ P) (en : P) (ex : WindowExit → P) {c m : ℕ} (p : Fin c)
    {x : List Γ} (fs : List (List Γ)) (hfs : fs.length = m)
    (d : Cfg (K + 2) Γ (Σ i : cw_Idx c m, cw_Ctrl P i) x) (hrec : RecordAt d 0 fs)
    (hclk : ∀ z, d.workTapes (Fin.last (K + 1)) z = none) (j : ℕ) (hj : j < fs.length)
    (n r : ℕ) (hnr : n + fs[j].length + 1 ≤ r) (hor : fieldOffset fs (j + 1) ≤ r) :
    Segment (cw_hostTM e R en ex c m) {z | ∃ y : WindowExit, z = some ⟨.stop, y⟩}
      (cw_box d.workTapePos r)
      (cw_cfg e d (⟨.copy p ⟨j, hfs ▸ hj⟩, (SweepPhase.sweep : SweepPhase)⟩ :
        Σ i, cw_Ctrl P i) (fieldOffset fs j) n n)
      (cw_cfg e d (cw_next p ⟨j, hfs ▸ hj⟩) (fieldOffset fs (j + 1)) (n + fs[j].length)
        ((n + fs[j].length : ℕ) : ℤ)) (4 * fs[j].length + 9) := by
  have hoff := fieldOffset_succ fs j hj
  have hfield := cw_field d 0 fs hrec j hj
  have hor' : ((fieldOffset fs (j + 1) : ℕ) : ℤ) ≤ r := by exact_mod_cast hor
  have habs : |((fieldOffset fs (j + 1) : ℕ) : ℤ)| ≤ r := by
    rw [abs_of_nonneg (by positivity)]
    exact hor'
  have s₁ := cw_seg_copy e R en ex p ⟨j, hfs ▸ hj⟩ d fs[j] (fieldOffset fs j) n
    (n + fs[j].length) r hfield rfl (by positivity) (by omega) (by omega)
  have s₂ := cw_seg_skipS e R en ex p ⟨j, hfs ▸ hj⟩ d fs[j] (fieldOffset fs j)
    (fieldOffset fs (j + 1)) (n + fs[j].length) n r
    (fun z hz₁ hz₂ => hfield z (by omega) hz₂) (by omega) (by positivity) hor'
    (by rw [abs_of_nonneg (by positivity)]; omega)
  have s₃ := cw_seg_skipC e R en ex (some (p, ⟨j, hfs ▸ hj⟩)) d hclk (fieldOffset fs (j + 1))
    (n + fs[j].length) n fs[j].length rfl ((n : ℤ) + fs[j].length + 1) rfl r habs (by omega)
  have s₄ := cw_seg_left e R en ex p ⟨j, hfs ▸ hj⟩ d (fieldOffset fs (j + 1))
    (n + fs[j].length) ((n : ℤ) + fs[j].length + 1) ((n + fs[j].length : ℕ) : ℤ)
    (by push_cast; ring) r habs (by omega) (by omega)
  exact cw_seg_time (s₁.trans (s₂.trans (s₃.trans s₄))) (by ring)

/-- **H3 with the configuration-count clock** (what `Complexity.space_hierarchy`'s
diagonalizer cites). The windowed runner that builds its own clock. For a fixed binary machine
`M` and a tag update `upd` that ignores silent steps, there is a module over the record alphabet
with an entry and three distinct exits `exit e`, as follows. Start it at its entry with the
record of a windowed configuration `c` with tag `τ` at the head of tape `0`, every other tape
blank, and the native input `x` as digits. Then it reaches an exit `exit out` within
`C · 2^(C·(L + 1))` steps, where `L` is the record length, and no exit earlier. Up to then
every head stays within `C · (L + 1)` cells of its entry position, so the space used is `O(L)`
with constants depending only on `M` and `upd`, and the output is unchanged. Moreover:
* **the configuration count suffices**: if `N ≤ configBound M |x| s + 1` rounds of
  `Turing.windowRun` stop, then `out` is their exit, and the stopping record is on tape `0`;
* if `out` is `halted` or `left`, it is the exit of a stopping `Turing.windowRun`, whose record
  is on tape `0`, with every other tape blank again and every head and the input position
  restored.

With `Turing.windowRun_summary_of_halts`, a halting run of `M` within `s` cells and
`configBound M |x| s` steps is reported as `halted` with its output's tag. The bound
`N ≤ configBound + 1` contains the extra halt-test round (the RD-3 gate's check 4). [AB09,
§4.1.3, Theorem 4.8 with Exercise 4.1; §4.1.1, Claim 4.4; the construction is the repository's
refinement]

**Proof sketch.** The statement does not fix the clock, and two routes meet it.

*Route A (one shared clock).* Build the clock word, then run `Turing.exists_windowRunnerTM` on
it, then clear it. The clock word is all `true` of width `W := c_M · L`: by
`Turing.FinTM.configBound_le_two_pow`, the configuration count is at most
`2 ^ (|Q| + posWidth |x| + 3k(2s + 1))`, the per-round cost is
`C · (L + |x| + 1) ≤ C · 2^(L + 1)` (since `|x| + 2 ≤ 2^(posWidth |x|)` and
`posWidth |x| ≤ L`), and `L ≥ k(2s + 1) + posWidth |x|`; so `2^W - 1` exceeds
`C · (configBound + 1) · (L + |x| + 1)` for a constant `c_M` depending only on `|Q|` and `C`
(`L ≥ 4`). The word is written by copying the record's layout `c_M` times onto a scratch tape
and mapping every cell to `digit true` (`Turing.copyTM`, `Turing.skipTM`, `Turing.scanTM`, as
S1b's plan does, design §12.8a §4 step 5); it costs `O(L)` cells and time. After a `halted` or
`left` exit, clear the clock (`Turing.clearTM_run_ofCfg`) and rewind its head.

*Route B (the round clock, proved today; the RD-3 gate's minor 3).* Run the window round (the
test row, then the step row) as the body of `Turing.counterLoopTMVia`, with the anchor at the
round's start and the halt and window exits merged into its one optional early exit
(`Turing.counterLoopTMVia_run_escape`), clock exhaustion being `done`
(`Turing.counterLoopTMVia_run_done`); after an escape, one more test row tells `halted` from
`left` on the unchanged record. The clock word has width `|Q| + posWidth |x| + 3k(2s + 1) + 1`
or more, so its value exceeds `configBound M |x| s`: rounds, not steps, are counted, and the
time is at most the clock value times `C · (L + |x| + 1)` (`Turing.counterLoop_time_le`).

**Implementation status.** The private `cw_` lemmas prove the clock arithmetic at the actual
record. `cw_field_total` counts the record's field cells, `k(2s + 1) + posWidth |x| + 2`, and
`cw_record_clock` shows that the all-true word over `c = C + |Q| + 8` passes of them has width
at most `c · L` and a value large enough for every round up to `configBound + 1`, the extra
halt-test round included (`C` is the runner's constant). The clock is Route A's over field
cells, of width `W = c · F ≤ c · L`, where `F` counts the field cells. The fields are separated
by blank cells and a mapped copy reads one blank-delimited word, so the clock is written one
field at a time and the separators are skipped, not written; the construction over the whole
layout sketched above (`W := c_M · L`, by `Turing.copyTM` and `Turing.scanTM`) is an alternative
that is not implemented. Everything runs on one phase host (`cw_hostTM`), whose phases are the
writer's rows, the windowed runner, the clear of the clock and the exits. Proved so far: one
field's round (`cw_round`): the constant copy of the field onto the clock at the clock head, the
skips past the field on the record tape and past the written cells on the clock, and the
one-cell move back onto the clock's right delimiter, the new cells joining the clock word by
`Turing.wordPatch_append`. This target remains open.
**Proof sketch (remaining).** Concatenate the rounds over the fields into a pass and the `c`
passes, the record head returning by skips back over the fields after each pass, and return the
clock head to the clock's first cell. Then run `Turing.exists_windowRunnerTM` on the word, clear
the clock after a `halted` or `left` exit (`cw_clear_patch`), and dispatch to the exits. The
time and head bounds follow from the clock budget and the linear writer and clear costs
(`cw_time_bound`, `cw_head_bound`), the silence from the endpoint, and the space bound from the
head bound (`Turing.MultiTapeTM.spaceUsed_le_of_abs_le`).
 -/
theorem exists_configWindowRunnerTM (M : FinTM Bool) {T : Type} [Fintype T] [DecidableEq T]
    (upd : T → Option Bool → T) (hupd : ∀ τ, upd τ none = τ) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 1) (RecSym M.State T) P) (entry : P) (exit : WindowExit → P)
      (C : ℕ),
      (∀ e, exit e ≠ entry) ∧ Function.Injective exit ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : T), c.InWindow s →
      ∀ d : Cfg (K + 1) (RecSym M.State T) P (x.map (RecSym.digitEmb M.State T)),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ (t : ℕ) (out : WindowExit),
          t ≤ C * 2 ^ (C * (recordLength M.k x.length s + 1)) ∧
          (R.runFrom d t).state = some (exit out) ∧
          (∀ u < t, ∀ e, (R.runFrom d u).state ≠ some (exit e)) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 1), |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ u ≤ t, (R.runFrom d u).output = d.output) ∧
          R.spaceUsed d t ≤ (K + 1) * (2 * C * (recordLength M.k x.length s + 1) + 1) ∧
          (∀ N ≤ M.configBound x.length s + 1, (windowRun M.tm s upd N c τ).1 ≠ .exhausted →
            out = (windowRun M.tm s upd N c τ).1) ∧
          (out ≠ .exhausted → ∃ N, (windowRun M.tm s upd N c τ).1 = out ∧
            R.runFrom d t =
              { d with
                state := some (exit out)
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos 0 ≤ q ∧
                      q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
                    then fieldsTape (cfgRecord s (windowRun M.tm s upd N c τ).2.1
                      (windowRun M.tm s upd N c τ).2.2) (q - d.workTapePos 0)
                  else d.workTapes j q }) := by
  sorry

end Turing
