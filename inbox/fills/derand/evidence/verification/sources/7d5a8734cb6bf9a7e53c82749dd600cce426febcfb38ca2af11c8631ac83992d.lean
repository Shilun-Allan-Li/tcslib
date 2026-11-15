/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.SymbolLift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the symbol lift

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
A contract of an input-oblivious `Bool` machine that never writes a blank becomes a contract of
its symbol lift on any rich configuration, through `Turing.Cfg.decodeSymbols`
(`Turing.MultiTapeTM.liftSymbols_runFrom_over`, `Turing.Cfg.liftOver_decodeSymbols`).

## Main definitions

* `Turing.Contract.liftSymbols`.

## Main results

The fields of `Turing.Contract.liftSymbols` are its results: the lifted run reaches the overlaid
endpoint at the source time, never meets an exit earlier, and keeps the source envelope.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the specification-only calls adapted as `Turing.Contract` (design adaptation; full
  entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **The symbol lift** (`Turing.MultiTapeTM.liftSymbols_runFrom_over`, through
`Turing.Cfg.decodeSymbols`): a contract of an input-oblivious `Bool` machine that never writes a
blank, on the `Bool` shadow of the input, becomes a contract of its lift on any rich
configuration. The precondition, the time and the envelope are the source's at the decoded
shadow; the endpoint is the source endpoint overlaid on the rich start, so every rich cell the
source run did not change keeps its symbol.

**Proof sketch.** Every rich configuration is the overlay of its shadow on itself
(`Turing.Cfg.liftOver_decodeSymbols`), and the overlay commutes with the run
(`Turing.MultiTapeTM.liftSymbols_runFrom_over`). The overlay keeps the state and the heads, so
the exit, the cut and the envelope are the source's. -/
def Contract.liftSymbols [DecidableEq Γ] (e : Bool ↪ Γ) {S : Type} {N : MultiTapeTM k Bool S}
    (hin : ∀ q inp inp' work, N.tr q inp work = N.tr q inp' work)
    (hnb : ∀ q inp work j, ((N.tr q inp work).workTapes j).1 ≠ some none)
    {entry : S} {X : Set (Option S)} {ι : Type} {x : List Γ}
    (C : Contract N entry X ι (x.map fun _ => false)) :
    Contract (N.liftSymbols e) entry X ι x where
  pre i D := C.pre i (Cfg.decodeSymbols e D)
  time i D := C.time i (Cfg.decodeSymbols e D)
  post i D := Cfg.liftOver e (by simp) D (C.post i (Cfg.decodeSymbols e D))
  lo i D := C.lo i (Cfg.decodeSymbols e D)
  hi i D := C.hi i (Cfg.decodeSymbols e D)
  run i D hD hp := by
    have hr := MultiTapeTM.liftSymbols_runFrom_over e N hin hnb (by simp) D
      (Cfg.decodeSymbols e D) (C.time i (Cfg.decodeSymbols e D))
    rw [Cfg.liftOver_decodeSymbols] at hr
    rw [hr, C.run i _ hD hp]
  exit_mem i D hD hp := C.exit_mem i _ hD hp
  cut i D hD hp u hu := by
    have hr := MultiTapeTM.liftSymbols_runFrom_over e N hin hnb (by simp) D
      (Cfg.decodeSymbols e D) u
    rw [Cfg.liftOver_decodeSymbols] at hr
    rw [hr]
    exact C.cut i _ hD hp u hu
  env i D hD hp u hu j := by
    have hr := MultiTapeTM.liftSymbols_runFrom_over e N hin hnb (by simp) D
      (Cfg.decodeSymbols e D) u
    rw [Cfg.liftOver_decodeSymbols] at hr
    rw [hr]
    exact C.env i _ hD hp u hu j

end Turing
