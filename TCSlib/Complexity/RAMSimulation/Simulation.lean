/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NondeterministicSpace
import TCSlib.Complexity.RAMSimulation.Sim.Startup
import TCSlib.Complexity.RAMSimulation.Sim.Phases
import TCSlib.Complexity.RAMSimulation.Sim.RunInput
import TCSlib.Complexity.RAMSimulation.Sim.RunBranch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2: the word RAM on Turing machines

A program `P` of the extended word RAM (`WordRAM.XProgram`) runs on an input `x`, a coin stream
`ρ` and a word size `W = W (|x|)`. One finite binary Turing machine simulates its
instructions with the following bounds, where `n = |x|`:

* time `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`;
* space `SW n + A·(f·(W + 1) + W + logSpace n + 1)`.

Here `t` bounds the RAM's steps, `f` bounds the number of cells it touches, and the word size is
computed within time `TW` and space `SW` (`WordRAM.WordSizeComputable`). The constant may depend
on the program, output mode and word-size witness, but not on the input or its resource bounds.
The nondeterministic form uses one binary choice per `coin`, with bounds uniform over streams.
Both constructions use the finite phase host and the shared run induction.

**Bounds and model.** An address computed by `load` or `store` is a word's signed value; the
program's immediate addresses are fixed integers (`WordRAM.Sim.ImmBound`). A memory-table entry
therefore has `W + O_P(1)` bits. Input access uses `Turing.exists_inputSeekTM`, whose time is
linear in the position and input length. The word-size computation's time and space costs are
added once, using the silent embedding `Turing.embedSilentTM`.

## Main definitions

* `WordRAM.simTime`, `WordRAM.simSpace`: the time and space bounds, with readers `simTime_eq`
  and `simSpace_eq`.
* `WordRAM.outputOf`: the verdict or emitted word, with readers `outputOf_false` and
  `outputOf_true`.

## Main results

* `WordRAM.exists_simulation`: stage 2, deterministic form.
* `WordRAM.exists_ndSimulation`: stage 2, nondeterministic form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9, p. 35: a RAM Turing machine is simulated with
  polynomial overhead; §2.1.2: NDTMs; Definition 4.1; §4.3.1: read-once certificates.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0: the word RAM of
  `EndStatement.lean` (vendored as `TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`, is the simulated model.
-/

namespace WordRAM

/-- **The time bound of stage 2**: computing the word size, then `t + 1` simulated steps, each at
most one scan of a table of `f` entries of `W + O(1)` bits, one shift-and-add multiplication of
`W`-bit words, and one input seek. -/
def simTime (A : ℕ) (TW : ℕ → ℕ) (n W t f : ℕ) : ℕ :=
  TW n + A * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1)

/-- **The space bound of stage 2**: computing the word size, then the memory table (`f` entries
of `W + O(1)` bits), `O(1)` words of scratch, and the input length in binary. -/
def simSpace (A : ℕ) (SW : ℕ → ℕ) (n W f : ℕ) : ℕ :=
  SW n + A * (f * (W + 1) + W + Complexity.logSpace n + 1)

/-- What the stage-2 machine leaves on its output tape: in verdict mode (`fn = false`) the
one-bit verdict, as `Turing.FinTM.DecidesInTime` and `Turing.FinTM.DecidesInSpace` read it; in
function mode (`fn = true`) the emitted word, as `Turing.FinTM.ComputesInSpace` reads it. -/
def outputOf (fn v : Bool) (o : List Bool) : List Bool := if fn then o else [v]

/-- The time bound, as an equation:
`simTime A TW n W t f = TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`. -/
theorem simTime_eq (A : ℕ) (TW : ℕ → ℕ) (n W t f : ℕ) :
    simTime A TW n W t f = TW n + A * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1) := rfl

/-- The space bound, as an equation:
`simSpace A SW n W f = SW n + A·(f·(W + 1) + W + logSpace n + 1)`. -/
theorem simSpace_eq (A : ℕ) (SW : ℕ → ℕ) (n W f : ℕ) :
    simSpace A SW n W f = SW n + A * (f * (W + 1) + W + Complexity.logSpace n + 1) := rfl

/-- In verdict mode the output is the one-bit verdict. -/
theorem outputOf_false (v : Bool) (o : List Bool) : outputOf false v o = [v] := rfl

/-- In function mode the output is the emitted word. -/
theorem outputOf_true (v : Bool) (o : List Bool) : outputOf true v o = o := rfl

/-- **Stage 2, deterministic form** (design §15a, §16b; backlog PROG-4). For every program `P` of
the extended word RAM, every output mode `fn` and every word size `W` computable within `TW` and
`SW`, there are a finite binary machine `M` and a constant `A` such that: whenever `P`, run on
`x` with word size `W (|x|)` and the empty coin stream (coins read `0`), gives the verdict `v`
within `t` steps, having emitted `o` and touched at most `f` cells, then `M` halts on `x` within
`TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` steps with `outputOf fn v o` on its output tape,
having visited at most `SW n + A·(f·(W + 1) + W + logSpace n + 1)` work cells (`n = |x|`).
[AB09, Exercise 1.9]

Deviations: [AB09] has a RAM Turing machine with a symbol array and the bound `T(n)²`; this is
[AFM26]'s word RAM with input, output and coins, and the bound is explicit in steps, cells and
word size. From design §15a's draft shape: no separate address width, a seek term `n` rather than
`n·log n`, and the word size's own cost added (module docstring).

**Proof sketch.** Choose the finite phase host with `Sim.exists_runSetup`, and fix its choices
to false. `Sim.RunSetup.input_run` combines startup with the shared execution induction,
whose exact touched-cell set is bounded by the source halting witness. Every consumed coin
is false, so the stream is the empty stream. Its schedule word is a constant false word;
`Sim.runWith_replicate` and `Sim.runSpace_replicate` transfer its run and visited cells to the
deterministic slice. The common head envelope and fixed setup coefficient give the stated
bounds. Halting preserves the space bound at the final, possibly larger, time. -/
theorem exists_simulation (P : XProgram) (fn : Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) :
    ∃ (M : Turing.FinTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ) (v : Bool) (o : List Bool),
      HaltsWithin P x [] (W x.length) t v o f →
        M.ComputesInTime x (outputOf fn v o) (simTime A TW x.length (W x.length) t f) ∧
        M.tm.spaceUsed (M.tm.initCfg x) (simTime A TW x.length (W x.length) t f) ≤
          simSpace A SW x.length (W x.length) f := by
  obtain ⟨Mw, hMw⟩ := (wordSizeComputable_iff W TW SW).mp hW
  obtain ⟨A⟩ := Sim.exists_runSetup P fn Mw
  let M : Turing.FinTM Bool := ⟨8 + A.extraTapes, A.State, A.host.fixChoice false⟩
  refine ⟨M, A.boundCost, ?_⟩
  intro x t f v o hh
  obtain ⟨tw, htw, hcomp, hspace⟩ := hMw x
  let D : Sim.RunDriver (W x.length) := Sim.RunDriver.ofSchedule (fun _ => false)
  let B : ℕ → Bool → Prop := fun _ b => b = false
  have hD : D.Respects B := by
    rw [Sim.RunDriver.respects_iff]
    intro s c
    exact Sim.RunDriver.ofSchedule_coin (fun _ => false) s c
  have hhalt : ∀ coins, Sim.RunCoinsSatisfy B coins →
      ∃ ρ, Sim.RunCoinsAgree coins ρ ∧ ∃ v' out,
        HaltsWithin P x ρ (W x.length) t v' out f ∧ (v' = v ∧ out = o) := by
    intro coins hc
    refine ⟨[], ?_, v, o, hh, rfl, rfl⟩
    rw [Sim.runCoinsAgree_iff]
    intro i hi
    rw [List.getD_nil]
    exact (Sim.runCoinsSatisfy_iff B coins).mp hc i hi
  obtain ⟨w, e, ρ, v', out, _, ⟨hv, hout⟩, hr, hd, ho, ht, hs, hf⟩ :=
    A.input_run x tw (SW x.length) t f hcomp hspace D B hD (fun _ v' out => v' = v ∧ out = o) hhalt
  subst v'
  subst out
  have hrep : w = List.replicate w.length false :=
    (hf (fun _ => false) (Sim.RunDriver.ofSchedule_follows _)).trans
      (Sim.runChoices_const false 0 w.length)
  have hinit : M.tm.initCfg x = A.host.initCfg x := by
    change (A.host.fixChoice false).initCfg x = A.host.initCfg x
    rw [Turing.MultiTapeTM.initCfg_eq, Turing.NDTM.initCfg_eq, Turing.NDTM.fixChoice_q₀]
  have hrun : M.tm.runFrom (M.tm.initCfg x) w.length = e := by
    change (A.host.fixChoice false).runFrom (M.tm.initCfg x) w.length = e
    rw [hinit, ← Sim.runWith_replicate, ← hrep]
    exact hr
  have hc : M.ComputesInTime x (outputOf fn v o) w.length :=
    (Turing.FinTM.computesInTime_iff _ _ _ _).mpr
      ⟨by rw [hrun]; exact hd, by rw [hrun]; simpa only [outputOf] using ho⟩
  have hsM : M.tm.spaceUsed (M.tm.initCfg x) w.length ≤
      simSpace A.boundCost SW x.length (W x.length) f := by
    change (A.host.fixChoice false).spaceUsed (M.tm.initCfg x) w.length ≤ _
    rw [hinit, ← Sim.runSpace_replicate, ← hrep, simSpace_eq]
    exact hs
  have htM : w.length ≤ simTime A.boundCost TW x.length (W x.length) t f := by
    rw [simTime_eq]
    exact ht.trans (Nat.add_le_add_right htw _)
  exact ⟨hc.mono htM, hc.spaceUsed_le_of_halt hsM _⟩

/-- **Stage 2, nondeterministic form** (design §15c, §16b item 4; backlog PROG-4). For every
program `P` of the extended word RAM and every word size `W` computable within `TW` and `SW`,
there are a finite binary nondeterministic machine `N` and a constant `A` such that: if, on the
input `x`, **every** coin stream lets `P` give a verdict within `t` steps touching at most `f`
cells (bounds uniform over the streams, as `NTIME` and `NSPACE` require), then every branch of
`N` of length `T = simTime …` has halted, every such branch has visited at most `simSpace …` work
cells, and `N` accepts `x` within `T` exactly when some coin stream makes `P` accept.
[AB09, Exercise 1.9 with §2.1.2 and Definition 4.1; the coins are read once, as the certificate
of §4.3.1]

**Proof sketch.** Use `Sim.exists_runSetup` in verdict mode. For each choice word,
`Sim.RunSetup.branch_run` reads its timed schedule, extracts the consumed coins and applies
uniform source halting. It gives both a halted endpoint and the common visited-cell bound.
An accepting endpoint therefore supplies an accepting source stream. Conversely the
`Sim.RunDriver.ofCoins` driver places a prescribed accepting stream's next bit at each coin
entry. `Sim.RunSetup.input_run` constructs the accepting branch within the same time bound;
`Turing.FinNDTM.AcceptsWithin.mono` pads it to the exact stated length. -/
theorem exists_ndSimulation (P : XProgram) {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) :
    ∃ (N : Turing.FinNDTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ),
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool), HaltsWithin P x ρ (W x.length) t v o f) →
        N.tm.HaltsWithin x (simTime A TW x.length (W x.length) t f) ∧
        (∀ w : List Bool, w.length = simTime A TW x.length (W x.length) t f →
          N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ simSpace A SW x.length (W x.length) f) ∧
        (N.AcceptsWithin x (simTime A TW x.length (W x.length) t f) ↔
          ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o f) := by
  obtain ⟨Mw, hMw⟩ := (wordSizeComputable_iff W TW SW).mp hW
  obtain ⟨A⟩ := Sim.exists_runSetup P false Mw
  let N : Turing.FinNDTM Bool := ⟨8 + A.extraTapes, A.State, A.host⟩
  refine ⟨N, A.boundCost, ?_⟩
  intro x t f hhalt
  obtain ⟨tw, htw, hcomp, hspace⟩ := hMw x
  have hbranches : ∀ w : List Bool,
      w.length = simTime A.boundCost TW x.length (W x.length) t f →
      ∃ ρ v out, HaltsWithin P x ρ (W x.length) t v out f ∧
        (N.tm.runWith w (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith w (N.tm.initCfg x)).output = [v] ∧
        N.tm.spaceUsedWith w (N.tm.initCfg x) ≤
          simSpace A.boundCost SW x.length (W x.length) f := by
    intro w hw
    have hlen : tw + A.boundCost * (t + 1) *
        (f * (W x.length + 1) + W x.length ^ 2 + x.length + 1) ≤ w.length := by
      rw [hw, simTime_eq]
      exact Nat.add_le_add_right htw _
    simpa only [N, simSpace_eq, Bool.false_eq_true, if_false] using
      A.branch_run x tw (SW x.length) t f hcomp hspace hhalt w hlen
  refine ⟨Turing.NDTM.haltsWithin_iff.mpr ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨_, _, _, _, hd, _, _⟩ := hbranches w hw
    exact hd
  · intro w hw
    obtain ⟨_, _, _, _, _, _, hs⟩ := hbranches w hw
    exact hs
  · constructor
    · intro hacc
      obtain ⟨w, hw, _, hout⟩ := Turing.FinNDTM.acceptsWithin_iff.mp hacc
      obtain ⟨ρ, v, out, hρ, _, hv, _⟩ := hbranches w hw
      have hvtrue : v = true := List.singleton_inj.mp (hv.symm.trans hout)
      exact ⟨ρ, out, by rw [hvtrue] at hρ; exact hρ⟩
    · rintro ⟨ρ, out, hρ⟩
      let D : Sim.RunDriver (W x.length) := Sim.RunDriver.ofCoins ρ
      let B : ℕ → Bool → Prop := fun i b => b = ρ.getD i false
      have hsource : ∀ coins, Sim.RunCoinsSatisfy B coins →
          ∃ τ, Sim.RunCoinsAgree coins τ ∧ ∃ v out',
            HaltsWithin P x τ (W x.length) t v out' f ∧ (v = true ∧ out' = out) := by
        intro coins hc
        exact ⟨ρ, (Sim.runCoinsAgree_iff coins ρ).mpr
          ((Sim.runCoinsSatisfy_iff B coins).mp hc), true, out, hρ, rfl, rfl⟩
      obtain ⟨u, e, _, v, out', _, ⟨hv, ho⟩, hr, hd, hout, ht, _, _⟩ :=
        A.input_run x tw (SW x.length) t f hcomp hspace D B
          (Sim.RunDriver.ofCoins_respects ρ) (fun _ v out' => v = true ∧ out' = out) hsource
      subst v
      subst out'
      have hacc : N.AcceptsWithin x u.length := Turing.FinNDTM.acceptsWithin_iff.mpr
        ⟨u, rfl, by rw [hr]; exact hd, by rw [hr]; exact hout⟩
      apply hacc.mono
      rw [simTime_eq]
      exact ht.trans (Nat.add_le_add_right htw _)

end WordRAM
