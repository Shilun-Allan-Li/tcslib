/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Phases
import Mathlib.Data.List.GetD

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Source-run facts for the RAM simulation

These facts read extended RAM steps through `WordRAM.xstep_def` and the run readers. They
connect instruction fetch, coin consumption and the exact footprint to the host induction.

## Main definitions

No new source-machine operation is defined here.

## Main results

* `WordRAM.Sim.source_pc_lt`: a non-verdict step is at a position inside the program.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

/-- A step that continues instead of giving a verdict must fetch inside the program;
the default instruction past the end rejects. -/
theorem source_pc_lt {W : ℕ} {P : XProgram} {x ρ : List Bool} {c c' : XCfg W}
    (h : xstep P x ρ c = .inl c') : c.pc < P.length := by
  by_contra hp
  rw [xstep_def, List.getD_eq_default P (.base .reject) (Nat.le_of_not_gt hp)] at h
  cases h

/-- A source step depends on a stream only through the bit at its current coin counter, and
only when the fetched instruction is a coin. -/
theorem source_step_coin_congr {W : ℕ} (P : XProgram) (x ρ τ : List Bool) (c : XCfg W)
    (hbits : isCoin (P.getD c.pc (.base .reject)) = true →
      ρ.getD c.rd false = τ.getD c.rd false) :
    xstep P x ρ c = xstep P x τ c := by
  rw [xstep_def, xstep_def]
  cases hf : P.getD c.pc (.base .reject) with
  | base i => cases i <;> rfl
  | rdIn i j => rfl
  | emit i => rfl
  | coin i => rw [hbits (by rw [hf, isCoin_def])]
  | half i j => rfl

/-- A stream agrees with a finite consumed coin prefix at every index already present in
that prefix. The stream may be shorter if its default false bits give the same values. -/
def RunCoinsAgree (coins ρ : List Bool) : Prop :=
  ∀ i < coins.length, coins.getD i false = ρ.getD i false

/-- Agreement of consumed coins means equality of their defaulted reads at every consumed
index. This is the defining equivalence of `RunCoinsAgree`. -/
theorem runCoinsAgree_iff (coins ρ : List Bool) :
    RunCoinsAgree coins ρ ↔ ∀ i < coins.length, coins.getD i false = ρ.getD i false := Iff.rfl

/-- Every finite coin prefix agrees with itself. -/
theorem runCoinsAgree_refl (coins : List Bool) : RunCoinsAgree coins coins := fun _ _ => rfl

/-- Agreement with an extended consumed prefix implies agreement with the earlier prefix. -/
theorem runCoinsAgree_append_left (coins extra ρ : List Bool)
    (h : RunCoinsAgree (coins ++ extra) ρ) : RunCoinsAgree coins ρ := by
  rw [runCoinsAgree_iff] at h ⊢
  intro i hi
  have h' := h i (by rw [List.length_append]; omega)
  rw [List.getD_append coins extra false i hi] at h'
  exact h'

/-- An exact non-verdict source trace records precisely the union of the cells touched by
its instructions, rather than an arbitrary enclosing footprint. This internal relation lets
the branch induction compare its accumulated table cells with a `HaltsWithin` witness. -/
inductive RunSourceTrace {W : ℕ} (P : XProgram) (x ρ : List Bool) :
    ℕ → XCfg W → XCfg W → Finset ℤ → Prop
  | nil (c : XCfg W) : RunSourceTrace P x ρ 0 c c ∅
  | cons {n : ℕ} {c c₁ c' : XCfg W} {K : Finset ℤ}
      (step : xstep P x ρ c = .inl c₁) (tail : RunSourceTrace P x ρ n c₁ c' K) :
      RunSourceTrace P x ρ (n + 1) c c' ((P.getD c.pc (.base .reject)).touches c.mem ∪ K)

/-- An exact source trace is a footprint run inside any set containing its touched cells.

**Proof sketch.** Induct on the exact trace. Each constructor records the current instruction's
touch set unioned with the tail's cells, so the enclosing-set hypothesis supplies both the
current footprint clause and the tail induction hypothesis in `XStepsIn.succ_iff`. -/
theorem RunSourceTrace.to_stepsIn {W : ℕ} {P : XProgram} {x ρ : List Bool}
    {n : ℕ} {c c' : XCfg W} {K : Finset ℤ} (h : RunSourceTrace P x ρ n c c' K)
    (L : Set ℤ) (hK : ∀ z ∈ K, z ∈ L) : XStepsIn P x ρ L n c c' := by
  induction h generalizing L with
  | nil c => exact XStepsIn.zero_iff.mpr rfl
  | cons hs ht ih =>
    apply XStepsIn.succ_iff.mpr
    refine ⟨_, hs, ?_, ih L ?_⟩
    · intro z hz
      exact hK z (Finset.mem_union.mpr (Or.inl hz))
    · intro z hz
      exact hK z (Finset.mem_union.mpr (Or.inr hz))

/-- An exact non-verdict prefix of a run that eventually halts has no more steps than the
halting run, and all of its touched cells belong to the halting run's footprint.

**Proof sketch.** Compare the exact trace with the `XStepsIn` witness one step at a time.
If the halting witness has zero remaining ordinary steps, a further exact step contradicts
its verdict. Otherwise determinism identifies the first successor, the footprint clause
bounds this step's cells, and the induction hypothesis bounds the remaining prefix. This is
the prefix/footprint comparison; completed verdicts are compared with `HaltsWithin.unique`. -/
theorem RunSourceTrace.bounded_by_halt {W : ℕ} {P : XProgram} {x ρ : List Bool}
    {n : ℕ} {c c' : XCfg W} {K : Finset ℤ} (h : RunSourceTrace P x ρ n c c' K)
    {L : Set ℤ} {m : ℕ} {c₂ : XCfg W} {v : Bool}
    (hr : XStepsIn P x ρ L m c c₂) (hv : xstep P x ρ c₂ = .inr v) :
    n ≤ m ∧ ∀ z ∈ K, z ∈ L := by
  induction h generalizing m c₂ with
  | nil c =>
    refine ⟨Nat.zero_le _, ?_⟩
    intro z hz
    exact (Finset.notMem_empty z hz).elim
  | cons hs ht ih =>
    cases m with
    | zero =>
      have heq := XStepsIn.zero_iff.mp hr
      subst c₂
      have hbad := hs.symm.trans hv
      cases hbad
    | succ m =>
      obtain ⟨d, hd, hcells, htail⟩ := XStepsIn.succ_iff.mp hr
      have heq := Sum.inl.inj (hs.symm.trans hd)
      subst d
      obtain ⟨hn, hK⟩ := ih htail hv
      refine ⟨Nat.succ_le_succ hn, ?_⟩
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hcells hz
      · exact hK z hz

/-- Agreement with a consumed prefix ending in `b` makes the stream's read at that newly
consumed index equal to `b`, including when the earlier prefix is empty. -/
theorem runCoinsAgree_append_bit (coins ρ : List Bool) (b : Bool)
    (h : RunCoinsAgree (coins ++ [b]) ρ) : ρ.getD coins.length false = b := by
  rw [runCoinsAgree_iff] at h
  have h' := h coins.length (by rw [List.length_append, List.length_singleton]; omega)
  rw [List.getD_append_right coins [b] false coins.length le_rfl, Nat.sub_self] at h'
  change b = ρ.getD coins.length false at h'
  exact h'.symm

/-- A continuing source step increments the coin counter exactly for a coin instruction. -/
theorem source_step_rd {W : ℕ} {P : XProgram} {x ρ : List Bool} {c c' : XCfg W}
    (h : xstep P x ρ c = .inl c') :
    c'.rd = c.rd + (if isCoin (P.getD c.pc (.base .reject)) then 1 else 0) := by
  rw [xstep_def] at h
  split at h <;> cases h <;>
    simp_all only [isCoin_def, reduceCtorEq, if_true, if_false, Nat.add_zero]

/-- An instruction giving a verdict is not a coin, so it consumes no stream bit. -/
theorem source_verdict_not_coin {W : ℕ} {P : XProgram} {x ρ : List Bool}
    {c : XCfg W} {v : Bool} (h : xstep P x ρ c = .inr v) :
    isCoin (P.getD c.pc (.base .reject)) = false := by
  rw [xstep_def] at h
  split at h <;> cases h <;> simp_all only [isCoin_def]

/-- A source verdict remains the same under any replacement of the coin stream. -/
theorem source_verdict_stream {W : ℕ} {P : XProgram} {x ρ : List Bool}
    {c : XCfg W} {v : Bool} (h : xstep P x ρ c = .inr v) (τ : List Bool) :
    xstep P x τ c = .inr v := by
  apply (source_step_coin_congr P x τ ρ c ?_).trans h
  intro hc
  rw [source_verdict_not_coin h] at hc
  cases hc

/-- Every consumed coin in a prefix satisfies the indicated predicate at its index. -/
def RunCoinsSatisfy (B : ℕ → Bool → Prop) (coins : List Bool) : Prop :=
  ∀ i < coins.length, B i (coins.getD i false)

/-- A prefix satisfies its indexed coin predicate exactly at its consumed indices. -/
theorem runCoinsSatisfy_iff (B : ℕ → Bool → Prop) (coins : List Bool) :
    RunCoinsSatisfy B coins ↔ ∀ i < coins.length, B i (coins.getD i false) := Iff.rfl

/-- The empty consumed prefix satisfies every indexed coin predicate. -/
theorem runCoinsSatisfy_nil (B : ℕ → Bool → Prop) : RunCoinsSatisfy B [] :=
  fun i hi => (Nat.not_lt_zero i hi).elim

/-- Appending a permitted bit at the next coin index preserves the indexed coin predicate. -/
theorem runCoinsSatisfy_append (B : ℕ → Bool → Prop) (coins : List Bool) (b : Bool)
    (h : RunCoinsSatisfy B coins) (hb : B coins.length b) : RunCoinsSatisfy B (coins ++ [b]) := by
  rw [runCoinsSatisfy_iff] at h ⊢
  intro i hi
  by_cases hip : i < coins.length
  · rw [List.getD_append coins [b] false i hip]
    exact h i hip
  · have hie : i = coins.length := by rw [List.length_append, List.length_singleton] at hi; omega
    subst i
    rw [List.getD_append_right coins [b] false coins.length le_rfl, Nat.sub_self]
    change B coins.length b
    exact hb

/-- The consumed coin prefix after one instruction: append its entry bit for a coin, and
keep the prefix for every other instruction. -/
def runNextCoins (ins : XInstr) (coins : List Bool) (b : Bool) : List Bool :=
  if isCoin ins then coins ++ [b] else coins

/-- The next consumed prefix is given by the instruction's coin test. -/
theorem runNextCoins_eq (ins : XInstr) (coins : List Bool) (b : Bool) :
    runNextCoins ins coins b = if isCoin ins then coins ++ [b] else coins := rfl

/-- A consumed prefix grows by exactly one bit for a coin and by zero otherwise. -/
theorem runNextCoins_length (ins : XInstr) (coins : List Bool) (b : Bool) :
    (runNextCoins ins coins b).length = coins.length + (if isCoin ins then 1 else 0) := by
  cases hc : isCoin ins <;>
    simp only [runNextCoins_eq, hc, reduceCtorEq, if_true, if_false,
      List.length_append, List.length_singleton, Nat.add_zero]

/-- The next consumed prefix extends the current one, by either an empty suffix or one bit. -/
theorem runNextCoins_prefix (ins : XInstr) (coins : List Bool) (b : Bool) :
    ∃ extra, runNextCoins ins coins b = coins ++ extra := by
  cases hc : isCoin ins with
  | false =>
    refine ⟨[], ?_⟩
    simp only [runNextCoins_eq, hc, reduceCtorEq, if_false, List.append_nil]
  | true =>
    refine ⟨[b], ?_⟩
    simp only [runNextCoins_eq, hc, if_true]

/-- A stream agreeing with the next consumed prefix supplies the selected entry bit whenever
the instruction is a coin. -/
theorem runNextCoins_read (ins : XInstr) (coins ρ : List Bool) (b : Bool)
    (h : RunCoinsAgree (runNextCoins ins coins b) ρ) :
    isCoin ins = true → ρ.getD coins.length false = b := by
  intro hc
  apply runCoinsAgree_append_bit coins ρ b
  simpa only [runNextCoins_eq, hc, reduceCtorEq, if_true] using h

/-- Updating the consumed prefix preserves its indexed predicate when the selected next bit
is permitted. Non-coin instructions leave that prefix unchanged. -/
theorem runNextCoins_satisfy (B : ℕ → Bool → Prop) (ins : XInstr) (coins : List Bool) (b : Bool)
    (h : RunCoinsSatisfy B coins) (hb : B coins.length b) :
    RunCoinsSatisfy B (runNextCoins ins coins b) := by
  cases hc : isCoin ins with
  | false => simpa only [runNextCoins_eq, hc, reduceCtorEq, if_false] using h
  | true => simpa only [runNextCoins_eq, hc, reduceCtorEq, if_true] using
      runCoinsSatisfy_append B coins b h hb

end WordRAM.Sim
