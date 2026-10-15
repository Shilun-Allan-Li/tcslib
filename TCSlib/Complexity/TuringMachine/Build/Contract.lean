/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
import TCSlib.Complexity.TuringMachine.Build.Contract.Embed
import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog
import TCSlib.Complexity.TuringMachine.Build.Contract.Lift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts

**Status: the MIG-0a structure landed on 2026-10-13, after its gate closed at round 2**
(`audits/mig0a-findings.md`, `audits/mig0a-r2-findings.md`; resolutions
`audits/mig0a-resolutions.md`). **MIG-0b landed after its gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`): this file is the facade of
the layering split (design §16a item 4), and MIG-0a's content moved, with no statement
changed, into the children below. Everything they hold is proved.

A *contract* packages what the library's framed rows state one by one (design §14 item 0,
§16): started at `entry` in a configuration satisfying the precondition, the machine reaches
the endpoint after **exactly** a given time, has **not** reached an exit before, and keeps every
work head inside an interval. The core adds segments, rounds and joint trajectories.

## Contents

* `TCSlib.Complexity.TuringMachine.Build.Contract.Basic` — the core: `Turing.Contract`, the
  frame layer, `Turing.ReturnContract`, the segment, round and joint-trajectory layers, the
  sanity lemmas, state renaming and the macro-step lockstep. It imports only the machine core.
* `TCSlib.Complexity.TuringMachine.Build.Contract.Seam` — `seq`, `inPhase`, `branch` and the
  release adapters over `Build/Seam`, with their trajectories, frames and positivity.
* `TCSlib.Complexity.TuringMachine.Build.Contract.Embed` — `embed` over `Build/Embed`.
* `TCSlib.Complexity.TuringMachine.Build.Contract.Catalog` — R3 clear as a contract.
* `TCSlib.Complexity.TuringMachine.Build.Contract.Lift` — the symbol lift.

Elsewhere, beside the machinery they adapt: the counter loop over round contracts in
`Build/CounterLoop`; and the exports of the split in `Finite`
(`MultiTapeTM.spaceUsedByTape_le_card_Icc`, moved from `Build/Catalog`, and
`MultiTapeTM.workTapePos_runFrom_mem_Icc`), `StateRenaming`
(`MultiTapeTM.runFrom_mapState_of_agreeOn`, moved from `Build/Embed`), `Build/Embed` (the R1
reconstruction lemma) and `Build/Seam` (the right segment and the release lockstep). The
alphabet-reduction adapter (alphabet reduction as a `Turing.Lockstep`, with its
contract-to-contract theorem) lands with RS-5 in `Robustness/AlphabetReduction`, together with
its proof.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: design adaptation, full entry in `Build/Contract/Basic`.
-/
