# Seal inventory and exclusions

The full source is sealed at `seal-list.txt`: 36 foreign TCSlib definitions. The fresh
`EPadForeignDefs` walk enumerates definitions occurring in every compiled Padding declaration's
type and value, including private and generated declarations; `EPadCites` supplies their modules.
The fresh inventory is exactly 46 definitions: the 36 seals and ten listed exclusions. Explicit simp/rw/unfold arguments were
also inspected, since irreducibility does not prevent an explicit named unfold.

| Excluded constant(s) | Reason and limit |
|---|---|
| `Complexity.LogProg.ARM`, `AConf`, `BankS` | Published reducible `abbrev`s. The standards allow reading their bodies; Lean's normal reducibility validation rejects a local irreducibility attribute. No unsafe reducibility override is used. |
| `Complexity.LogProg.Ins.casesOn` | Generated eliminator for the instruction inductive, marked reducible. Pattern matching on the published instruction constructors uses it. Attribute rejection is tested separately; this is not claimed as an effective seal. |
| `Complexity.LogProg.alignedPair_loop.match_1` | Generated matcher in a published statement. Lean's matcher reduction is still available after the attribute; the dedicated control demonstrates this limitation. It is excluded explicitly, rather than counted among sealed definitions. |
| `Turing.FinTM.State`, `decEqState`, `fintypeState`, `k`, `tm` | Public structure projections, verified against the structure source in Finite. Their field use is the published structure interface. |

The full-file sealed proof, both control forms, fresh inventory and the separate limitation
probes are distinct checks. The positive control must close 36 pointwise equations and 36
parameter-abstracted equations. The sealed control must fail all 72 at default transparency, with
no unexpected errors or successful reflexivity attempts.

The original delivery's exclusions are retained separately in `delivery-not-sealed.txt`. A copied
`[-simp]` attribute for `Turing.NDTM.initCfg` was absent after import cleanup; the failed attempt is
retained. The final copy removes the reachable definition unfoldings `Turing.Action.apply`,
`Turing.Cfg.init` and `Turing.MultiTapeTM.initCfg`, reconciled with the fresh simp-definition walk.
These are proof-environment changes only, not library edits.
