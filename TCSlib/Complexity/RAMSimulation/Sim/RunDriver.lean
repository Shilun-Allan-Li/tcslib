/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunSource
import TCSlib.Complexity.RAMSimulation.Sim.RunChoices

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Choosing words for one shared simulation induction

A driver selects an entry coin, a word of any requested phase length beginning with that
choice, and a dispatch bit. Later choices in an instruction do not affect its behavior. A
driver may therefore read an arbitrary timed schedule, or place a prescribed RAM stream's
bits at phase entries. The same execution induction applies to both.

## Main definitions

* `WordRAM.Sim.RunDriver`: entry choices and finite phase words.
* `WordRAM.Sim.RunDriver.Follows`: the words and dispatches come from one timed schedule.
* `WordRAM.Sim.RunDriver.Respects`: each consumed coin satisfies an indexed predicate.

## Main results

The two driver modes share the phase correctness and resource arguments.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2: binary branches; §4.3.1: read-once coins.)
-/

namespace WordRAM.Sim

/-- A choice driver supplies each phase's entry bit and a word of the requested length with
that first bit when nonempty. Its dispatch bit is consumed by the stationary host redirect. -/
structure RunDriver (W : ℕ) where
  coin : ℕ → XCfg W → Bool
  word : ℕ → XCfg W → ℕ → List Bool
  word_length : ∀ s c n, (word s c n).length = n
  word_head : ∀ s c n, 0 < n → (word s c n).headD false = coin s c
  dispatch : ℕ → Bool

namespace RunDriver

/-- A driver follows schedule `χ` when every phase word and dispatch bit is read from it at
the appropriate absolute time. -/
def Follows {W : ℕ} (D : RunDriver W) (χ : ℕ → Bool) : Prop :=
  (∀ s c n, D.word s c n = runChoices χ s n) ∧ ∀ s, D.dispatch s = χ s

/-- Following a schedule means the stated phase-word and dispatch equations. -/
theorem follows_iff {W : ℕ} (D : RunDriver W) (χ : ℕ → Bool) :
    D.Follows χ ↔ (∀ s c n, D.word s c n = runChoices χ s n) ∧ ∀ s, D.dispatch s = χ s := Iff.rfl

/-- A driver respects a coin predicate when its chosen entry bit satisfies that predicate
at the current source coin counter, for every time and source configuration. -/
def Respects {W : ℕ} (D : RunDriver W) (B : ℕ → Bool → Prop) : Prop :=
  ∀ s c, B c.rd (D.coin s c)

/-- Respecting a coin predicate is the corresponding pointwise entry-choice condition. -/
theorem respects_iff {W : ℕ} (D : RunDriver W) (B : ℕ → Bool → Prop) :
    D.Respects B ↔ ∀ s c, B c.rd (D.coin s c) := Iff.rfl

/-- The driver obtained by reading one absolute-time choice schedule. The source configuration
is irrelevant to its choices, so every constructed word is an actual slice of that schedule. -/
@[simps (config := { isSimp := false }) coin word dispatch]
def ofSchedule {W : ℕ} (χ : ℕ → Bool) : RunDriver W where
  coin s _ := χ s
  word s _ n := runChoices χ s n
  word_length s _ n := runChoices_length χ s n
  word_head s _ n hn := runChoices_head χ s n hn
  dispatch := χ

/-- The schedule driver follows its defining schedule. -/
theorem ofSchedule_follows {W : ℕ} (χ : ℕ → Bool) :
    (ofSchedule χ : RunDriver W).Follows χ := ⟨fun _ _ _ => rfl, fun _ => rfl⟩

/-- The driver placing a prescribed RAM stream's next bit at each instruction entry, with
constant phase words and false dispatch bits. It produces a realizing branch, rather than
assuming the prescribed stream was already present on a tape. -/
@[simps (config := { isSimp := false }) coin word dispatch]
def ofCoins {W : ℕ} (ρ : List Bool) : RunDriver W where
  coin _ c := ρ.getD c.rd false
  word _ c n := List.replicate n (ρ.getD c.rd false)
  word_length _ c n := List.length_replicate
  word_head _ c n hn := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [List.replicate_succ]
    rfl
  dispatch _ := false

/-- The prescribed-stream driver chooses the prescribed defaulted bit at every coin index. -/
theorem ofCoins_respects {W : ℕ} (ρ : List Bool) :
    (ofCoins ρ : RunDriver W).Respects (fun i b => b = ρ.getD i false) := fun _ _ => rfl

end RunDriver

end WordRAM.Sim
