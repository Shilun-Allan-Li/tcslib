/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Choice-tape determinization: the replay machine

An NDTM run along a choice word is a deterministic run that reads the word from a tape: the
**replay machine** `Turing.NDTM.replayTM N` has one extra work tape, the *choice tape*, which it
reads at every step (a blank reads as `false`) to select the transition function, moving the
choice head right and never writing it. The replay lemma `Turing.NDTM.replayTM_runFrom`
identifies its runs with `N`'s branches. This is the certificate view of nondeterminism
([AB09, §2.1.2, Theorem 2.6]: the choices of an accepting branch are a certificate that a
deterministic verifier checks by simulation).

## Design

* **No new machinery is needed to interpret nondeterministic codes.** A coded NDTM's replay
  machine is a deterministic three-work-tape machine, so its fixed `k`-record serialization
  (`Turing.serializeK`) is interpreted by the deterministic step block (host H2) at `k = 3`,
  unchanged (user decision 3 of 2026-10-13; the C1 design note §3.2, option (c)).
* **Consumers:** the per-code replay canonizer and the interpreter core
  (`TCSlib.Complexity.TuringMachine.NDCodeSimulator`) and the exhaustive replay
  (`TCSlib.Complexity.ClassNP.ExhaustiveReplay`). It can also replace the private choice-word
  replay of `TCSlib.Complexity.ClassNP.Nondeterminism` (the C1 design note §3.5, inferred).

## Main definitions

* `Turing.NDTM.replayTM` — the replay machine. [AB09, §2.1.2]
* `Turing.NDTM.withChoiceTape` — an NDTM configuration extended by a choice tape.

## Main results

* `Turing.NDTM.replayTM_runFrom` — the replay lemma (proved).
* The fields of the replay machine `Turing.NDTM.replayTM_q₀`, `_tr` and of the extended
  configuration `Turing.NDTM.withChoiceTape_state`, `_inputPos`, `_workTapes`, `_workTapePos`,
  `_output` (the ND inventory API, C1's pre-ship inventory, 2026-10-17).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, Theorem 2.6 and its proof.)
-/

namespace Turing.NDTM

variable {k : ℕ} {S : Type*}

/-- **The replay machine** of an NDTM `N` with `k` work tapes: the deterministic machine with
`k + 1` work tapes that, at every step, reads the choice tape (the last one; a blank reads as
`false`), applies the corresponding transition function of `N` to the first `k` tapes, and
moves the choice head one cell right without writing it. Its states, initial state, input moves
and output are `N`'s. [AB09, §2.1.2: a branch of an NDTM is its run along a choice word; the
verifier of Theorem 2.6 reads that word] -/
def replayTM (N : NDTM k Bool S) : MultiTapeTM (k + 1) Bool S where
  q₀ := N.q₀
  tr := fun q inp w =>
    let a := N.tr ((w (Fin.last k)).getD false) q inp (fun i => w i.castSucc)
    ⟨a.inputTape, Fin.lastCases (none, 1) a.workTapes, a.output, a.state⟩

/-! The replay machine's fields as equations (the ND inventory API, 2026-10-17), by `simps` without
the `simp` attribute: `N.replayTM.q₀ = N.q₀`, and `N.replayTM.tr q inp w` is the action of
`N.tr ((w (Fin.last k)).getD false) q inp (fun i => w i.castSucc)` on the first `k` tapes, with the
choice tape unwritten and its head moved right. -/
attribute [simps (config := { isSimp := false }) q₀ tr] replayTM

/-- The configuration `c` of an NDTM extended by a choice tape `ct` with its head at `cp` as the
last work tape; every other field is `c`'s. -/
def withChoiceTape {x : List Bool} (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) :
    Cfg (k + 1) Bool S x :=
  ⟨c.state, c.inputPos, Fin.lastCases ct c.workTapes, Fin.lastCases cp c.workTapePos, c.output⟩

/-! The extended configuration's fields as equations (the ND inventory API, 2026-10-17), by `simps`
without the `simp` attribute: the state, input head and output are `c`'s, and
`(withChoiceTape c ct cp).workTapes = Fin.lastCases ct c.workTapes`,
`(withChoiceTape c ct cp).workTapePos = Fin.lastCases cp c.workTapePos`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  withChoiceTape

/-- **The replay lemma.** With the word `s` on the choice tape from cell `0`, the replay
machine's run for `t ≤ |s|` steps is the NDTM's branch along `s.take t`, extended by the
unchanged choice tape, with the choice head at some `p ≤ t`, and at exactly `t` while that
branch is live (the head stops when the branch halts). [AB09, §2.1.2]

**Proof sketch.** Induct on `t`. A live step reads `s[t]` under the choice head at `t`, so the
replay machine applies `N.tr s[t]` to the first `k` tapes and moves the choice head; a halted
step is the identity on both sides (`Turing.NDTM.runWith_of_halt`). -/
theorem replayTM_runFrom {x : List Bool} (N : NDTM k Bool S) (c : Cfg k Bool S x)
    (s : List Bool) (t : ℕ) (ht : t ≤ s.length) :
    ∃ p ≤ t, ((N.runWith (s.take t) c).state ≠ none → p = t) ∧
      N.replayTM.runFrom (withChoiceTape c (FinTM.bufferTape s) 0) t =
        withChoiceTape (N.runWith (s.take t) c) (FinTM.bufferTape s) p := by
  induction t with
  | zero => exact ⟨0, le_rfl, fun _ => rfl, rfl⟩
  | succ t ih =>
    obtain ⟨p, hp, hlive, hrun⟩ := ih (by omega)
    have htake : s.take (t + 1) = s.take t ++ [s[t]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun, htake, runWith_append]
    cases hs : (N.runWith (s.take t) c).state with
    | none =>
      refine ⟨p, by omega, ?_, ?_⟩
      · intro h
        exact absurd (by rw [runWith_of_halt _ hs]; exact hs) h
      · rw [runWith_of_halt _ hs]
        exact MultiTapeTM.step_of_halt (by simp [withChoiceTape, hs])
    | some q =>
      have hpt : p = t := hlive (by simp [hs])
      subst hpt
      refine ⟨p + 1, le_rfl, fun _ => rfl, ?_⟩
      set e := N.runWith (s.take p) c with he
      have hread : (withChoiceTape e (FinTM.bufferTape s) (p : ℤ)).workTapeSymbols
          (Fin.last k) = some (s[p]'(by omega)) := by
        simp [withChoiceTape, Cfg.workTapeSymbols, FinTM.bufferTape]
      have hwork : (fun i : Fin k =>
          (withChoiceTape e (FinTM.bufferTape s) (p : ℤ)).workTapeSymbols i.castSucc) =
          e.workTapeSymbols := by
        funext i
        simp [withChoiceTape, Cfg.workTapeSymbols]
      have hinp : (withChoiceTape e (FinTM.bufferTape s) (p : ℤ)).inputSymbol =
          e.inputSymbol := rfl
      unfold MultiTapeTM.step
      have hst : (withChoiceTape e (FinTM.bufferTape s) (p : ℤ)).state = some q := by
        simp [withChoiceTape, hs]
      rw [hst]
      simp only [runWith_cons, runWith_nil]
      unfold stepWith
      rw [hs]
      simp only [replayTM]
      rw [hread, hwork, hinp]
      simp only [Option.getD_some]
      apply Cfg.ext
      · rfl
      · rfl
      · funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [withChoiceTape, Action.apply]
        · simp [withChoiceTape, Action.apply]
      · funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [withChoiceTape, Action.apply]
        · simp [withChoiceTape, Action.apply]
      · rfl

end Turing.NDTM
