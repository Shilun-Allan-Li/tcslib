/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the counter rows

**Status: proved (MIG-11a, user 2026-10-16).** The successful increment and decrement of a
fixed-width binary counter as contracts: the instances of MIG-11 that `Build/CfgRecord`'s
rebase onto the contract layer (MIG-12) composes. They sit in their own module, beside
`Build/CounterLoop` where the decrement is defined, so that `Build/Contract/Catalog` does not
import the counter loop.

## Main definitions

* `Turing.counterRowContract`: the contract of a successful counter row, from its framed
  theorem; `Turing.incrementTM_contract` and `Turing.decrementTM_contract` are its instances,
  indexed by the counter word and its successor (resp. predecessor), exiting at either verdict.

## Main results

* `Turing.counterRowContract_pre`, `_time`, `_post`, `_lo`, `_hi`, and the same for its two
  instances: their fields as equations, without the `simp` attribute (`policy.md` §1,
  *Definitions land with their lemmas*).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the contract shape, a design adaptation (full entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ}

/-- **The contract of a successful counter row** (MIG-11a, user 2026-10-16): one constructor for
the increment and the decrement. Given a machine `M` over `FlagPhase`, its tape `i`, the
width-preserving word map `fix` it computes and the bit `lead`-cells it carries through, and the
row's framed theorem `hrun`, this is the contract indexed by pairs `(w, v)` with `fix w = some v`
and `w` delimited at the head of tape `i`: time `2 · |takeWhile lead w| + 2`, endpoint the word's
interval holding `v` at `done true`, exits both verdicts, the head of tape `i` within
`[pos - 1, pos + |takeWhile lead w|]` and every other head fixed.

**Proof sketch.** Each field is the matching clause of `hrun`; the exit lies in the range at
`true`; a fixed head lies in its one-point interval. -/
def counterRowContract (M : MultiTapeTM k Bool FlagPhase) (i : Fin k) (x : List Bool)
    (fix : List Bool → Option (List Bool)) (lead : Bool → Bool)
    (hrun : ∀ (w v : List Bool), fix w = some v → ∀ (d : Cfg k Bool FlagPhase x),
      d.state = some FlagPhase.run →
      (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
        d.workTapes i (d.workTapePos i + q) = FinTM.bufferTape w q) →
      M.runFrom d (2 * (w.takeWhile lead).length + 2) =
          { d with
            state := some (FlagPhase.done true)
            workTapes := fun j q =>
              if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
                then FinTM.bufferTape v (q - d.workTapePos j)
              else d.workTapes j q } ∧
        (∀ t < 2 * (w.takeWhile lead).length + 2, ∀ b : Bool,
          (M.runFrom d t).state ≠ some (FlagPhase.done b)) ∧
        (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile lead).length + 2 →
          if j = i then
            (M.runFrom d t).workTapePos j ∈
              Finset.Icc (d.workTapePos j - 1)
                (d.workTapePos j + ((w.takeWhile lead).length : ℤ))
          else (M.runFrom d t).workTapePos j = d.workTapePos j)) :
    Contract M FlagPhase.run (Set.range fun b => some (FlagPhase.done b))
      (List Bool × List Bool) x where
  pre p d := fix p.1 = some p.2 ∧ ∀ q : ℤ, -1 ≤ q → q ≤ (p.1.length : ℤ) →
    d.workTapes i (d.workTapePos i + q) = FinTM.bufferTape p.1 q
  time p _ := 2 * (p.1.takeWhile lead).length + 2
  post p d := { d with
    state := some (FlagPhase.done true)
    workTapes := fun j q =>
      if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (p.1.length : ℤ)
        then FinTM.bufferTape p.2 (q - d.workTapePos j)
      else d.workTapes j q }
  lo p d j := if j = i then d.workTapePos j - 1 else d.workTapePos j
  hi p d j := if j = i then d.workTapePos j + ((p.1.takeWhile lead).length : ℤ)
    else d.workTapePos j
  run p d hd hp := (hrun p.1 p.2 hp.1 d hd hp.2).1
  exit_mem _ _ _ _ := ⟨true, rfl⟩
  cut p d hd hp u hu h := by
    obtain ⟨b, hb⟩ := h
    exact (hrun p.1 p.2 hp.1 d hd hp.2).2.1 u hu b hb.symm
  env p d hd hp u hu j := by
    have h := (hrun p.1 p.2 hp.1 d hd hp.2).2.2 j u hu
    split_ifs at h ⊢ with hj
    · exact h
    · rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- **The successful increment as a contract** (MIG-11a, user 2026-10-16): the counter-row
contract of `Turing.incrementTM` at `fix = incFixed` and `lead = id`. From the working phase,
with `incFixed w = some v` and `w` delimited at the head of tape `i`, the increment reaches
`done true` at exactly `2 · |takeWhile id w| + 2` (its leading `true` cells, each crossed twice,
and the two turning steps) with the word's interval holding `v`; no verdict earlier.

**Proof sketch.** `Turing.counterRowContract` with `Turing.incrementTM_run_succ_ofCfg`. -/
def incrementTM_contract (i : Fin k) (x : List Bool) :
    Contract (incrementTM k i) FlagPhase.run (Set.range fun b => some (FlagPhase.done b))
      (List Bool × List Bool) x :=
  counterRowContract (incrementTM k i) i x incFixed id (incrementTM_run_succ_ofCfg i)

/-- **The successful decrement as a contract** (MIG-11a, user 2026-10-16): the counter-row
contract of `Turing.decrementTM` at `fix = decFixed` and `lead = not`. From the working phase,
with `decFixed w = some v` and `w` delimited at the head of tape `i`, the decrement reaches
`done true` at exactly `2 · |takeWhile not w| + 2` (its leading `false` cells, each crossed
twice, and the two turning steps) with the word's interval holding `v`; no verdict earlier.

**Proof sketch.** `Turing.counterRowContract` with `Turing.decrementTM_run_succ_ofCfg`. -/
def decrementTM_contract (i : Fin k) (x : List Bool) :
    Contract (decrementTM k i) FlagPhase.run (Set.range fun b => some (FlagPhase.done b))
      (List Bool × List Bool) x :=
  counterRowContract (decrementTM k i) i x decFixed not (decrementTM_run_succ_ofCfg i)

/-! The specification API (user, 2026-10-16): the contracts' data fields as equations, generated
by `simps` without the `simp` attribute (`simps!` for the two instances, which are built through
`Turing.counterRowContract`). -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] counterRowContract
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  incrementTM_contract decrementTM_contract

end Turing
