# PR #122's body, as corrected 2026-10-17 (head `6a48b93e`; gate 41, minor 1)

## The ND inventory API, round 2

This PR repairs gate 37's findings 1 and 3 (#119, merged before its gate) and gate 38's minor 5
(#120). Its later commits add equations the reviews of C1 wave 1's first deliveries found
missing (2026-10-17), and gate 40's minor 1 docstring. The resolutions are in `audits/nd-api-resolutions.md` and
`audits/nd-normalform-resolutions.md`.

**It is stacked on #121** (`lean/ntime-diag` at `0a5878ed`), because the replay closures overlap.
Merge #121 first.

### What

Five commits. They add 22 public equations and change 3 docstrings. No statement, definition or proof
body changes, and no `@[simp]` is added.

| File | Change |
|---|---|
| `TuringMachine/Build/StepBlock` | `workReadsK_zero`, `workReadsK_succ`, `tableBitsK_eq`: the `k`-record table layout, in `workReadsK` order (finding 1) |
| `TuringMachine/CodeFormat` | `actionBitsK_eq` (a record's fields in tape order); `codeSkipActionK_append` (skipping a serialized record leaves its suffix) (finding 1) |
| `TuringMachine/Encoding` | the twelve case equations of `signBits`, `optBoolBits`, `optOptBoolBits` and `optStateBits` (finding 1) |
| `TuringMachine/Build/CounterLoop` | `counterValue_eq`: `counterValue w = Nat.ofDigits 2 (w.map Bool.toNat)`, the form of the hosted loop's value hypothesis (C1-R's E1; second commit) |
| `TuringMachine/CodeParser` | `codeBitsNat_eq`: `codeBitsNat xs = xs.foldr Nat.bit 0` (C1-R's E1; second commit) |
| `TuringMachine/Simulation` | `MultiTapeTM.agreeOn_iff` (C1-WC's review); `FinTM.bufferTape_eq` and `FinTM.bufferTape_of_neg` (the seam-layout contract's consumer); a Contents entry for each (third and fourth commits) |
| `TuringMachine/NDCodeSimulator` | the module Design bullet: R's prefix clause is kept with no consumer (gate 40, minor 1; fifth commit, docstring only) |
| `TuringMachine/Build/VirtualInput` | `vhostSilentCfg_eq`'s docstring: the capture tape holds `capPre` followed by `c.output`, and the physical output is `out₀` (finding 3) |
| `ClassNP` (facade) | the `## Contents` entry for `NDNormalForm` (gate 38, minor 5) |

Every new equation is `rfl` (`agreeOn_iff`: `Iff.rfl`) except two: `codeSkipActionK_append` goes
through `codeEraseActionK` and `codeReadActionK_append`, and `bufferTape_of_neg` rewrites with
`bufferTape_eq`. The first commit's statements are the review's draft
(`$S/review/nd-api-gate/probes/RCApiDraft.lean`). Its consumer, with every definition
irreducible, derives `workReadsK 3`'s order, the three-tape table and the choice field's bits.

### Checks (maintainer)

- **Elaboration**, each changed module against `oleans-lndnf`: 0 errors. `Encoding` has 1 warning,
  the existing `sorry` of `pairDiagTM_computes`; `Simulation` 1, the existing `branchTM_spaceUsed`;
  `NDCodeSimulator` its 2 contracts, as at the base. The other six have none. A probe in `CounterLoop`
  derives `Nat.ofDigits 2 ((Nat.bits t).map Bool.toNat) = t` from `counterValue_eq` and
  `counterValue_bits`.
- **Axioms:** the 12 encoder cases, `actionBitsK_eq`, `codeBitsNat_eq`, `agreeOn_iff` and
  `bufferTape_eq` use none; `bufferTape_of_neg` uses `propext` and `Quot.sound`.
  `counterValue_eq` uses `propext`. `workReadsK_zero`/`_succ` and
  `tableBitsK_eq` use `propext`. `codeSkipActionK_append` uses `propext` and `Quot.sound`.
- **Freeze:** 22 publics added, none removed, no private change. The only body change is
  `vhostSilentCfg_eq`'s docstring, which is authorized.
- **Lint:** 0 FAIL. `TuringMachine/` stays at 63 WARN, and `ClassNP/` at 15. Check 8 no longer lists
  `workReadsK`, `tableBitsK` (StepBlock), `actionBitsK`, `codeSkipActionK` (CodeFormat), `signBits`,
  `optBoolBits`, `optOptBoolBits` or `optStateBits` (Encoding). The second commit changes no lint row
  except `CounterLoop`'s line count. The third commit drops `AgreeOn` from `Simulation`'s check-8 row.
- **Screen** (8 files: the 4 changed modules with declarations, `CodeParser`, `CodeSimulator`,
  `NDCodes`, `NDCodeSimulator`): 337 → 337 declarations, 68 → 69 pairs. The one new pair,
  `NDCodes::CodeNDTM.serialize` reproducing `StepBlock::tableBitsK` (79/141 = 56%), is a
  boundary artifact. Both texts are unchanged. At the base, the screen counted the following
  `namespace StepBlock` (18 non-blank characters) into `tableBitsK`'s chunk (159). The new
  `tableBitsK_eq` now ends that chunk at 141, which lifts the same overlap over the 50% floor
  (79/159 at the base).
- **Replay:** `replay-lndapi2.sh`, 313 modules (`Simulation`'s closure, from the third commit;
  256 before), chained from `oleans-lndiag2` (#121 round 2's replay). **Passed (user,
  2026-10-17):** 313 of 313, static-equal (96).
- **Gate 41:** PASS 0/0/1/14 (`audits/nd-api-r2-findings.md`); its minor 1 is this paragraph and
  the head's lint (`r2/lint/lint-head-6a48b93e-*.txt`).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

