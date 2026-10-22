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

/-- A mapped copy of one field writes a constant symbol in the destination interval.
It requires delimiters only on the source, so it also appends to an existing clock prefix.
**Proof sketch.** Use the framed mapped copy. Every cell inside its write interval
has a valid source index; the constant merge ignores the old destination value. -/
private lemma cw_copy_constant {Γ : Type} {k : ℕ} {x : List Γ}
    (src dst : Fin k) (hne : src ≠ dst) (e : Γ) (w : List Γ)
    (d : Cfg k Γ SweepPhase x) (hd : d.state = some .sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (copyMapTM k src dst (fun _ => ()) (fun _ _ => e)).runFrom d (2 * w.length + 2) =
      { d with state := some .done
               workTapes := fun j q =>
                 if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
                   then some e else d.workTapes j q } := by
  have h := (copyMapTM_run_ofCfg src dst hne (fun _ => ()) (fun _ _ => e) w d hd hw).1
  rw [h]
  congr 1
  funext j q
  split_ifs with hi
  · have hn : 0 ≤ q - d.workTapePos j := by omega
    have hk : (q - d.workTapePos j).toNat < w.length := by omega
    rw [← Int.toNat_of_nonneg hn, FinTM.bufferTape_nat, List.getElem?_eq_getElem hk]
    rfl
  · rfl

/-- Clearing a word patch leaves its tape completely blank when the underlying tape
is blank outside the patch interval. Every other tape, all heads, the native input
position, and the output are preserved.
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
               workTapes := fun j q => if j = i then none else d.workTapes j q } := by
  dsimp only
  let a : Cfg k Γ SweepPhase x :=
    { d with state := some .sweep
             workTapes := fun j q => if j = i then
               wordPatch (d.workTapes j) (d.workTapePos j) w q else d.workTapes j q }
  change (clearTM k i).runFrom a (2 * w.length + 2) = _
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
  rw [(clearTM_run_ofCfg i w a rfl hw).1]
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
halt-test round included (`C` is the runner's constant). The one-cell left move (`cw_leftTM`,
`cw_left_run`), the constant mapped copy of one field (`cw_copy_constant`) and the clear of the
clock after the runner (`cw_clear_patch`, which leaves the clock tape blank) are proved. The
clock writer is not yet assembled, and this target remains open.
The clock these lemmas prepare is Route A's over field cells, of width `W = c · F ≤ c · L`,
where `F` counts the field cells. The fields are separated by blank cells and a mapped copy
reads one blank-delimited word, so the clock is copied one field at a time and the separators
are skipped, not written. The construction over the whole layout sketched above
(`W := c_M · L`, by `Turing.copyTM` and `Turing.scanTM`, which also read one blank-delimited
word) is an alternative that is not implemented; it would also have to handle the separators.
**Proof sketch (remaining).** Write the clock field by field: a constant mapped copy, a skip
past the field on each tape and a one-cell move back onto the clock's delimiter, joining
adjacent constant writes into one interval. Repeat for the `c` passes and rewind both heads.
Embed the writer on the record and clock tapes, run `Turing.exists_windowRunnerTM` on the word,
clear the clock after a `halted` or `left` exit, and dispatch to the exits. The time and head
bounds follow from the clock budget and the linear writer and clear costs, and
`Turing.windowRun_stop_unique` moves the certification to the statement's `N`.
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
