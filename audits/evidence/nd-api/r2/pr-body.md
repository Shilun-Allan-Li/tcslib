## The ND inventory API, round 2

This PR repairs gate 37's findings 1 and 3 (#119, merged before its gate) and gate 38's minor 5
(#120). The resolutions are in `audits/nd-api-resolutions.md` and
`audits/nd-normalform-resolutions.md`.

**It is stacked on #121** (`lean/ntime-diag` at `0a5878ed`), because the replay closures overlap.
Merge #121 first.

### What

One commit. It adds 17 public equations and changes 2 docstrings. No statement, definition or proof
body changes, and no `@[simp]` is added.

| File | Change |
|---|---|
| `TuringMachine/Build/StepBlock` | `workReadsK_zero`, `workReadsK_succ`, `tableBitsK_eq`: the `k`-record table layout, in `workReadsK` order (finding 1) |
| `TuringMachine/CodeFormat` | `actionBitsK_eq` (a record's fields in tape order); `codeSkipActionK_append` (skipping a serialized record leaves its suffix) (finding 1) |
| `TuringMachine/Encoding` | the twelve case equations of `signBits`, `optBoolBits`, `optOptBoolBits` and `optStateBits` (finding 1) |
| `TuringMachine/Build/VirtualInput` | `vhostSilentCfg_eq`'s docstring: the capture tape holds `capPre` followed by `c.output`, and the physical output is `out₀` (finding 3) |
| `ClassNP` (facade) | the `## Contents` entry for `NDNormalForm` (gate 38, minor 5) |

Every new equation is `rfl` except `codeSkipActionK_append`, which goes through
`codeEraseActionK` and `codeReadActionK_append`. The statements are the review's draft
(`$S/review/nd-api-gate/probes/RCApiDraft.lean`). Its consumer, with every definition
irreducible, derives `workReadsK 3`'s order, the three-tape table and the choice field's bits.

### Checks (maintainer)

- **Elaboration**, each changed module against `oleans-lndnf`: 0 errors. `Encoding` has 1 warning,
  the existing `sorry` of `pairDiagTM_computes`. The other four have none.
- **Axioms:** the 12 encoder cases and `actionBitsK_eq` use none. `workReadsK_zero`/`_succ` and
  `tableBitsK_eq` use `propext`. `codeSkipActionK_append` uses `propext` and `Quot.sound`.
- **Freeze:** 17 publics added, none removed, no private change. The only body change is
  `vhostSilentCfg_eq`'s docstring, which is authorized.
- **Lint:** 0 FAIL. `TuringMachine/` stays at 63 WARN, and `ClassNP/` at 15. Check 8 no longer lists
  `workReadsK`, `tableBitsK` (StepBlock), `actionBitsK`, `codeSkipActionK` (CodeFormat), `signBits`,
  `optBoolBits`, `optOptBoolBits` or `optStateBits` (Encoding).
- **Screen** (8 files: the 4 changed modules with declarations, `CodeParser`, `CodeSimulator`,
  `NDCodes`, `NDCodeSimulator`): 337 → 337 declarations, 68 → 69 pairs. The one new pair,
  `NDCodes::CodeNDTM.serialize` reproducing `StepBlock::tableBitsK` (79/141 = 56%), is a
  boundary artifact. Both texts are unchanged. At the base, the screen counted the following
  `namespace StepBlock` (18 non-blank characters) into `tableBitsK`'s chunk (159). The new
  `tableBitsK_eq` now ends that chunk at 141, which lifts the same overlap over the 50% floor
  (79/159 at the base).
- **Replay:** `replay-lndapi2.sh`, 256 modules, chained from `oleans-lndiag2` (#121 round 2's
  replay).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
