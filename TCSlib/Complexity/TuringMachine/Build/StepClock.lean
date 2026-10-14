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
# Machine-construction library: the step-clocked runner (host H3's clock)

A **step clock** runs a body machine under a binary countdown that ticks once per physical body
step. It exits at `finish` when the body stops (halts, or reaches a designated stop state), and
at `timeout` when the countdown is exhausted first. It is the clock of the windowed runner H3
(`machine-library-design.md` §14) and of the nondeterministic time hierarchy's diagonalizer
(C1, which cites the `Bool` instance `Turing.exists_stepClockTM`). Unlike the round counter
`Turing.counterLoopTMVia`, which restarts its body at a fixed anchor every round, it counts
physical steps, so the body's state survives from step to step.

**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). The layout definitions are real; the contract
`Turing.exists_stepClockTMVia` is sorried with its proof sketch, and its `Bool` instance is
proved from it.

## Design

* **Layout.** The body is on the first `k` tapes and the counter on the last
  (`Turing.clockCfg`). The counter digits are embedded along `e : Bool ↪ Γ`, as in
  `Turing.counterLoopTMVia`, so the clock runs over any alphabet with a digit embedding; the
  windowed runner runs over the record alphabet.
* **Exact endpoints.** At both exits the body part is the body's configuration at the stopping
  or clock time, and the counter tape differs from its start only on the counter word's cells,
  which hold some word of the same width (`Turing.wordPatch`).
* **Frames.** At every host time up to the exit, the body part (tapes, heads, input head,
  output) is the body's configuration at some body time, and the counter head stays within
  `[cp - 1, cp + |w|]`. This bounds the host's space by the body's plus `|w| + 2`, and carries
  silence and envelopes through the clock.
* The contract is an existential module; the named witness comes at fill time.

## Main definitions

* `Turing.clockCfg` — the host layout: body tapes first, the counter tape last.
* `Turing.wordPatch` — a tape with a word written over an interval.
* `Turing.Cfg.Stopped` — a body configuration that is halted or in a designated stop state.

## Main results

* `Turing.exists_stepClockTMVia` — the step clock over any alphabet (sorried).
* `Turing.exists_stepClockTM` — its `Bool` instance, in C1's draft form (proved from it).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, proof of Theorem 3.2: the diagonalizer runs the
  simulation for a bounded number of steps; §4.1.3, Theorem 4.8, whose proof the book assigns
  to Exercise 4.1. The fused step clock is the repository's refinement of that bounded
  simulation, not a construction printed in the book.)
-/

namespace Turing

/-- **The step clock's layout**: the body configuration `c` on the first `k` tapes, the
counter tape `ct` with its head at `cp` as the last tape, the host control `q`, and the body's
input head and output. -/
def clockCfg {k : ℕ} {Γ S Q : Type} {x : List Γ} (q : Option Q) (c : Cfg k Γ S x)
    (ct : ℤ → Option Γ) (cp : ℤ) : Cfg (k + 1) Γ Q x :=
  ⟨q, c.inputPos, Fin.lastCases ct c.workTapes, Fin.lastCases cp c.workTapePos, c.output⟩

/-- **A tape with a word patched in**: the cells `cp, …, cp + |u| - 1` hold `u`, every other
cell is `ct`'s. -/
def wordPatch {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ) : ℤ → Option Γ :=
  fun q => if cp ≤ q ∧ q < cp + (u.length : ℤ) then FinTM.bufferTape u (q - cp) else ct q

/-- **A stopped body configuration**: halted, or live in a designated stop state. -/
def Cfg.Stopped {k : ℕ} {Γ S : Type*} {x : List Γ} (stopAt : S → Bool) (c : Cfg k Γ S x) :
    Prop :=
  c.state = none ∨ ∃ s, c.state = some s ∧ stopAt s = true

/-- **H3's clock, the step-clocked runner** (joint statement with C1, whose draft
`exists_stepClockTM` is the instance `Γ = Bool`, `e = refl`; generalized to any alphabet with
a digit embedding, as the windowed runner runs over the record alphabet). For a body `M` with
designated stop states, there is a host on one more tape, with an injection `inj` of the body
states and two exit families `finish` and `timeout` carrying the body state, all distinct, as
follows. Start it at `inj q` with the body configuration `c` (live, at `q`) and a delimited
counter word `w` of value `d` (digits embedded by `e`) on the last tape.
* If the body first stops (halts, or reaches a stop state) at time `τ ≤ d`, the host reaches
  `finish` with the body's configuration at `τ`, within `5τ + 2|w| + 2` steps.
* If the body has not stopped by time `d`, the host reaches `timeout` with the body's
  configuration at time `d`, within `5d + 2|w| + 2` steps.

In both cases no exit occurs earlier; the counter tape differs from its start only on the
counter word's own cells, which hold some word of the same width, and its head is back at
`cp`; and at every host time up to the exit the host's body tapes, body heads, input head and
output are the body's at some body time no later than `τ` (or `d`), while the counter head
stays in `[cp - 1, cp + |w|]`. So the host's work space is the body's plus `|w| + 2`, and it
emits exactly what the body emits. This clock counts **physical body steps**, unlike the round
counter `Turing.counterLoopTMVia`, so a body's state survives from step to step. [AB09, §3.2,
proof of Theorem 3.2; §4.1.3, Theorem 4.8 with Exercise 4.1; the fused construction is the
repository's refinement]

**Proof sketch.** Fuse one decrement with every body transition: from `inj s`, if `s` is a stop
state go to `finish`; otherwise run the lifted decrement on the counter tape
(`Turing.decrementTM_run_succ_ofCfg` under `Turing.MultiTapeTM.liftSymbols`), whose success
anchor performs one body transition (the body tapes embedded by R1 along `Fin.castSucc`, as in
`Turing.counterLoopTMVia`) and returns to `inj` of the successor, or to `finish none` when the
transition halts the body; the decrement's underflow anchor is `timeout`. The decrement costs
sum to at most `4τ + 2|w|` (`Turing.counterOverhead_le_of_le`), plus the final underflow sweep
`2|w| + 2` in the timeout case (`Turing.counterOverhead_le`). The round induction is that of
`Turing.counterLoopTMVia_run_done` with one body step per round and an unrestricted body
state. A decrement moves only the counter head and writes only the counter tape, and a body
transition is the body's own step on the body tapes, which gives the frame clause. -/
theorem exists_stepClockTMVia {k : ℕ} {Γ S : Type} [Fintype S] [DecidableEq S]
    [DecidableEq Γ] (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (stopAt : S → Bool) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (k + 1) Γ Q)
      (inj : S → Q) (finish timeout : Option S → Q),
      Function.Injective finish ∧ Function.Injective timeout ∧
      (∀ a b, finish a ≠ timeout b) ∧ (∀ s r, inj s ≠ finish r ∧ inj s ≠ timeout r) ∧
      ∀ {x : List Γ} (c : Cfg k Γ S x) (q : S), c.state = some q →
      ∀ (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ),
        (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) →
        (∀ τ ≤ Nat.ofDigits 2 (w.map Bool.toNat), (M.runFrom c τ).Stopped stopAt →
          (∀ u < τ, ¬(M.runFrom c u).Stopped stopAt) →
          ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ w' : List Bool, w'.length = w.length ∧
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (finish (M.runFrom c τ).state)) (M.runFrom c τ)
                (wordPatch ct cp (w'.map e)) cp ∧
            (∀ u < T, ∀ r,
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) ∧
            ∀ u ≤ T, ∃ v ≤ τ,
              (∀ j : Fin k,
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapes j.castSucc =
                  (M.runFrom c v).workTapes j ∧
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos j.castSucc =
                  (M.runFrom c v).workTapePos j) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).inputPos =
                (M.runFrom c v).inputPos ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).output =
                (M.runFrom c v).output ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos (Fin.last k) ∈
                Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
        ((∀ u ≤ Nat.ofDigits 2 (w.map Bool.toNat), ¬(M.runFrom c u).Stopped stopAt) →
          ∃ T ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2,
            ∃ w' : List Bool, w'.length = w.length ∧
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (timeout (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))).state))
                (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat)))
                (wordPatch ct cp (w'.map e)) cp ∧
            (∀ u < T, ∀ r,
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) ∧
            ∀ u ≤ T, ∃ v ≤ Nat.ofDigits 2 (w.map Bool.toNat),
              (∀ j : Fin k,
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapes j.castSucc =
                  (M.runFrom c v).workTapes j ∧
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos j.castSucc =
                  (M.runFrom c v).workTapePos j) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).inputPos =
                (M.runFrom c v).inputPos ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).output =
                (M.runFrom c v).output ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos (Fin.last k) ∈
                Finset.Icc (cp - 1) (cp + (w.length : ℤ))) := by
  sorry

/-- **C1's step clock** (the `Bool` instance of `Turing.exists_stepClockTMVia`). This is the
statement of C1's draft `exists_stepClockTM` (`audits/evidence/c1/C1HostsDraft.lean.txt`, §4)
word for word: over `Bool`, with the counter tape's final contents left existential and without
the frame clause. It is proved here from the joint statement, so C1 may cite either.
[AB09, §3.2, proof of Theorem 3.2]

**Proof sketch.** Instantiate the joint statement at `e := Function.Embedding.refl Bool`
(`w.map e = w`) and forget the extra clauses. -/
theorem exists_stepClockTM {k : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (M : MultiTapeTM k Bool S) (stopAt : S → Bool) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (k + 1) Bool Q)
      (inj : S → Q) (finish timeout : Option S → Q),
      ∀ {x : List Bool} (c : Cfg k Bool S x) (q : S), c.state = some q →
      ∀ (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ),
        (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p) →
        let d := Nat.ofDigits 2 (w.map Bool.toNat)
        let stopped : Cfg k Bool S x → Prop := fun e =>
          e.state = none ∨ ∃ s, e.state = some s ∧ stopAt s = true
        (∀ τ ≤ d, stopped (M.runFrom c τ) → (∀ u < τ, ¬stopped (M.runFrom c u)) →
          ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ ct' : ℤ → Option Bool,
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (finish (M.runFrom c τ).state)) (M.runFrom c τ) ct' cp ∧
            ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠
              some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) ∧
        ((∀ u ≤ d, ¬stopped (M.runFrom c u)) →
          ∃ T ≤ 5 * d + 2 * w.length + 2, ∃ ct' : ℤ → Option Bool,
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (timeout (M.runFrom c d).state)) (M.runFrom c d) ct' cp ∧
            ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠
              some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) := by
  obtain ⟨Q, hQ, dQ, H, inj, finish, timeout, -, -, -, -, h⟩ :=
    exists_stepClockTMVia (Function.Embedding.refl Bool) M stopAt
  refine ⟨Q, hQ, dQ, H, inj, finish, timeout, ?_⟩
  intro x c q hq w ct cp hw
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    have hid : w.map (Function.Embedding.refl Bool) = w := by
      rw [Function.Embedding.coe_refl, List.map_id]
    rw [hid]
    exact hw
  obtain ⟨hfin, hto⟩ := h c q hq w ct cp hw'
  refine ⟨fun τ hτ hs hmin => ?_, fun hns => ?_⟩
  · obtain ⟨T, hT, w', -, hrun, hcut, -⟩ := hfin τ hτ hs hmin
    exact ⟨T, hT, _, hrun, hcut⟩
  · obtain ⟨T, hT, w', -, hrun, hcut, -⟩ := hto hns
    exact ⟨T, hT, _, hrun, hcut⟩

end Turing
