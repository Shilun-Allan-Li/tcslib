/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite oracle Turing machines

The bundled finite layer over `Turing.OracleTM`, mirroring `Turing.FinTM` over
`Turing.MultiTapeTM`: a `FinOracleTM` carries its state type with `Fintype` and
`DecidableEq` instances **as data**, and — unlike the raw layer — carries
`Turing.OracleTM.WellFormed` as a field, so that oracle complexity classes
(`Complexity.POracle`, `Complexity.NPOracle`; [AB09, Definition 3.5]) can never
quantify over a machine whose three special states collide. This discharges the
Chapter-1 obligation that "oracle complexity classes will introduce a finite
oracle-machine bundle before they are defined" (`AroraBarakChapter1Plan.md` §2).

## Design

* `WellFormed` is bundled, finiteness is bundled, the alphabet stays an explicit
  parameter — exactly the `FinTM` conventions. `q₀ = qQuery` remains deliberately
  allowed (such a machine submits the empty query on its first step).
* Time bounds are the only resource at this layer, mirroring
  `Turing.FinTM.ComputesInTime`; an oracle *space* measure is deliberately not
  introduced here (the chapters-3-4 campaign defines space for plain and
  nondeterministic machines first — `AroraBarakChapters3-4Plan.md` §2.4).
* The embedding of a plain bundled machine is `Turing.FinTM.toFinOracleTM`, the
  bundled form of `Turing.OracleTM.ofMultiTapeTM`; its behavior is
  oracle-independent and agrees with the plain machine
  (`toFinOracleTM_computesInTime`, proved here as a definitional-unfolding bridge
  over the audited `Turing.OracleTM.computesInTime_ofMultiTapeTM` — a
  skeleton-time proof, declared part of the audited surface per `workflow.md` §2).

## Main definitions

* `Turing.FinOracleTM` — the bundled, well-formed finite oracle machine.
  [AB09, Definition 3.4]
* `Turing.FinOracleTM.ComputesInTime`, `Turing.FinOracleTM.DecidesInTime` —
  output/decision within a time bound, relative to an oracle. [AB09, §3.4]
* `Turing.FinTM.toFinOracleTM` — a plain bundled machine as a bundled oracle
  machine that never queries.

## Main results

* `Turing.FinTM.toFinOracleTM_computesInTime` — the embedded machine's
  input/output behavior and time bounds are oracle-independent and agree with
  the plain machine's.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definitions 3.4-3.5.)
-/

namespace Turing

/-- A finite, well-formed oracle Turing machine over the alphabet `Symbol`: the raw
`Turing.OracleTM` bundled with `Fintype`/`DecidableEq` instances for its state type (as
data, since machine encodings must enumerate transition tables) and with the
`Turing.OracleTM.WellFormed` discipline (the three special states are pairwise
distinct) as a field. All oracle complexity classes are stated over this layer.
[AB09, Definition 3.4] -/
structure FinOracleTM (Symbol : Type) : Type 1 where
  /-- number of ordinary work tapes; the query tape is the extra work tape, giving
  `k + 1` work tapes in configurations -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying oracle machine -/
  tm : OracleTM k Symbol State
  /-- the three special states are pairwise distinct — bundled so that no oracle
  complexity class can forget it -/
  wf : tm.WellFormed

namespace FinOracleTM

attribute [instance] FinOracleTM.fintypeState FinOracleTM.decEqState

variable {Symbol : Type}

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape — the bundled form of `Turing.OracleTM.ComputesInTime`, mirroring
`Turing.FinTM.ComputesInTime` (time-only). -/
def ComputesInTime (M : FinOracleTM Symbol) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  M.tm.ComputesInTime O input output t

/-- The machine `M`, with oracle `O`, decides the language `L` within time `T`: on
every input `x` it halts within `T |x|` steps with output `[true]` if `x ∈ L` and
`[false]` otherwise — the oracle counterpart of `Turing.FinTM.DecidesInTime`.
[AB09, §3.4 with Definition 3.5] -/
def DecidesInTime (M : FinOracleTM Bool) (O : Language Bool) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime O x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end FinOracleTM

/-- A plain bundled machine as a bundled oracle machine that never queries: the
`FinTM` layer of `Turing.OracleTM.ofMultiTapeTM`, with the three special states
adjoined to the state type and well-formedness supplied by
`Turing.OracleTM.ofMultiTapeTM_wellFormed`. -/
def FinTM.toFinOracleTM {Symbol : Type} (M : FinTM Symbol) : FinOracleTM Symbol :=
  ⟨M.k, M.State ⊕ Fin 3, OracleTM.ofMultiTapeTM M.tm,
    OracleTM.ofMultiTapeTM_wellFormed M.tm⟩

/-- The embedded plain machine's behavior is oracle-independent and agrees with the
original: under **every** oracle `O`, the embedding computes `output` from `input`
within `t` steps iff the plain machine does. The bundled form of
`Turing.OracleTM.computesInTime_ofMultiTapeTM`, through
`Turing.FinTM.computesInTime_iff`; this is the sanity theorem behind
`Complexity.P_subset_POracle`. -/
theorem FinTM.toFinOracleTM_computesInTime {Symbol : Type} (M : FinTM Symbol)
    (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    M.toFinOracleTM.ComputesInTime O input output t ↔ M.ComputesInTime input output t := by
  rw [FinTM.computesInTime_iff]
  exact OracleTM.computesInTime_ofMultiTapeTM M.tm O input output t

end Turing
