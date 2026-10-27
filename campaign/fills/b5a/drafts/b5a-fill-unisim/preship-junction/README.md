# B5a, the uniform simulator: the loop junction, proved before issue (maintainer, 2026-10-27)

Gate 79 (round 1, finding 1; round 2, note 3) recorded this obligation for B5a's pre-ship: B5a
cites the interpreter startup `Turing.exists_interpreterStartup` (PR #169) at `p = F.k`, and the
junction from the startup's threshold into the hosted verdict `h1HostedVerdictTM F.k` reads
`CodeSimulator`'s private loop lemmas, so it is proved in a `CodeSimulator` overlay before B5a
issues. This folder proves it.

Tree: the campaign tip `36cc9fc0` (Lean as after #168's merge `13120e00`; snapshot `oleans-lu2m`).
The owned file's blob is `733a9a46`, unchanged since the pre-ship `../preship-a524c36f/`. The
probe does not need #169: it takes the startup's threshold fields as hypotheses, exactly as the
startup states them, so it holds for whatever machine reaches them. Lean ran through
`tools/leanelab.sh` against `oleans-lu2m`. Each `.out` is raw, with paths stripped.

| Check | Result | File |
|---|---|---|
| The junction probe | the overlay (`../preship-a524c36f/CodeSimulatorOverlay.lean.txt`, the brief's six imports) with the block inserted before `end MachineFormat`: exactly the target's sorry warning (overlay line 8660); `b5a_window_verdict`, `b5a_bank`, `b5a_junction`, `b5a_tail`, `b5a_start`, `b5a_run` on `[propext, Classical.choice, Quot.sound]`; 20.7 s, 2.57 GB. The overlay plus the block reproduces the elaborated file byte for byte (checked) | `B5aJunctionProbe.append.lean.txt`, `B5aJunctionProbe.out` |
| Standalone | `b5a_bank` and `b5a_junction` alone, importing `CodeSimulator` (no privates needed), under the same seal: 0 diagnostics, the standard three | `B5aJunctionDev.lean.txt`, `B5aJunctionDev.out` |
| Seal controls | the junction section's 20 sealed definitions (`MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `vhostCfg`, `counterLoopCfg`, `FinTM.bufferTape`, `tableBitsK`, `Cfg.init`, `Cfg.mapState`, `embedEmitCfg`, `embedEmitTM`, `seamCompTM`, `StepBlock.summaryCells`, `StepBlock.Rep`, `StepBlock.tableTape`, `StepBlock.summaryTape`, `StepBlock.exit`, `StepBlock.outputSummary`, `unaryFin`, `FinTM.ComputesInTime`, `pairEncode`; `-simp` on `MultiTapeTM.initCfg` and `Cfg.init`): unsealed all close; sealed all 20 fail, each at its own goal | `B5aJunctionSealControl.*` |

**What it proves** (the block's section `B5aUSJunction`, after the verdict probe's section):
- **`b5a_bank`** (generic in `k`): from the startup's role and passive indices and its ten
  separation facts, an embedding `g : Fin (1 + (k + 2 + 1)) ↪ Fin K` with
  - the window at `jwin`;
  - mirrored tape `i` at `ιP i`;
  - the table at `jtbl`, the summary at `jsm` and the counter at `jctr`.

  This is the hosted verdict's tape order: buffer, bank (mirrored tapes, table, summary),
  counter.
- **`b5a_junction`:** a configuration `c` with the startup's threshold fields at `p = F.k`, its
  state relabelled to the hosted clock's first state `(.dec .run, true)`, equals
  `embedEmitCfg g c.workTapes c.workTapePos [] (vhostCfg (counterLoopCfg (some (.dec .run)) d
  (bufferTape t.bits) 0) true c.inputPos [])`. Here `d` is at `StepBlock.exit F.k true`, with
  empty output, and `StepBlock.Rep`-represents the decoded machine's initial configuration on the
  window `x.take t`. That is exactly the start `h1HostedVerdict_accepts` takes.
- **`b5a_tail`:** given a run of `U` that first reaches `done` at such a configuration, the seam
  `seamCompTM U done (embedEmitTM g (h1HostedVerdictTM F.k)) (.dec .run, true)` halts within
  `T₁ + 1 + T₂` steps with output exactly `[answer]`. `T₂` is within the hosted verdict's bound,
  and `answer = true` iff the decoded machine accepts `x` (not the window) within `t`, by
  `b5a_window_verdict`, which is the window-to-`x` bridge.
- **`b5a_start`:** a composite over `Q ⊕ R`, restarted at `Sum.inl entry`, starts at the
  startup's blank start `⟨some entry, 1, blank, 0, []⟩` relabelled by `Sum.inl`
  (`initCfg_with_q₀`, the `Cfg.init` and `Cfg.mapState` fields).
- **`b5a_run`:** the binary machine `S : FinTM Bool` (the seam, restarted at `entry`; its
  state type's `Fintype` and `DecidableEq` instances are found) halts from
  `S.tm.initCfg ⟨⟨bits t, α⟩, x⟩` at `T₁ + 1 + T₂` with output `[answer]`: exactly the
  hypotheses of the route probe's `b5a_verdict`.

**For the brief:** route steps 1–4 (the header, the window, the table and the loop's entry)
become one citation of the startup at `p = F.k` with the installer `us_install`, `b5a_bank` on
its roles, and `b5a_run`. What remains for the fill is that citation, the choice of `S` and `d`
before the inputs, and the joint polynomial ledger with `b5a_verdict`. The probe's proofs may be copied as
`us_` privates.
