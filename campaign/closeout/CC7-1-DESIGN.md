# CC7-1 design note: the stage front's seven legs (2026-11-16)

For Seyoon's go/no-go. Family CC7-1 (`duplication-ledger.md`, "CC7-1, the canonizer cont7's
in-file families"); R3 row of `R3-R6-MEASUREMENT.md` (zero rule-10 exposure). The dead
`canonCounterRepeat` was retired in #336.

## What is there

`TuringMachine/CodeSimulator` (9,031 lines) proves its stage front one phase at a time. The seven
private lemmas `canonStageLeg0`–`canonStageLeg6` total **681 lines** with docstrings (89, 85, 90,
108, 105, 97 and 107). Each leg runs one public row machine on the outer-counter tape and proves
that the phase host hands control to the next phase with the expected bank.

| Leg | Row (public) | Effect on the outer counter |
|---|---|---|
| 0 | `copyTM_run_ofCfg` | writes the header word on a window |
| 1 | `skipTM_run_ofCfg` | moves the head right past the word |
| 2 | `walkTM_run_ofCfg` | moves the head one cell back |
| 3 | `writeConstTM_run_ofCfg` | writes `[false]` on a window |
| 4 | `skipTM_run_ofCfg` | moves the head right |
| 5 | `skipBackTM_run_ofCfg` | moves the head back to the origin |
| 6 | `incrementTM_run_succ_ofCfg` | writes the incremented word on a window |

Every leg has the same skeleton:

1. read the two bank configurations' fields (`canonStageBank_fields`, twice);
2. run the row;
3. call `phaseHostTM_run` with a dispatch proof and a guard proof;
4. close with `Cfg.ext`. State, input head and output are identical in every leg. The tape and
   head blocks differ only in how the row changed the outer counter.

Only the last part of step 4 is leg-specific, and it comes in two shapes. Copy, write-constant and
increment rewrite a window of the outer-counter tape (`{d with workTapes := fun j q => if j = i ∧
pos ≤ q ∧ q < pos + |w| then bufferTape w (q - pos) else …}`). Skip, skip-back and walk update the
outer counter's head (`{d with workTapePos := …}`).

## Proposal (all private, one file, no statement or API change)

- **`canonStageLeg_move` and `canonStageLeg_write`:** two private templates that take a row's run,
  cut and endpoint shape and return the leg's lockstep window and next bank. Each template calls
  `phaseHostTM_run` and does the whole `Cfg.ext` once. A leg then supplies its row, its dispatch
  and guard (two to six lines from the redirect table), and one cell-level fact: the new head
  position, or what the window write leaves on the tape.
- **`canonStageAt`:** a private abbreviation for "the bank at phase `i` in state `s`", which
  shortens the seven leg statements (each now repeats the 3-line bank expression four times).
- **One cut leg:** generalize `canonStageCut_leg` over the phase family, and let
  `canonGramCut_leg`, its 97% twin, cite it.

**Estimate.** The legs shrink to about 35–50 lines each and the templates cost about 120. That is
about **−250 to −320** Lean lines, with the four ≥ 90% leg/cut pairs gone.

**Cost and risk.** CodeSimulator sits under 23 modules, so the replay is small. Rule-10 exposure
is 0 (measured): the legs already read every other-file definition through published equations,
and the templates use the same ones. The leg statements' consumer (`canonStage_run`, the
`obtain ⟨hpre_i, hop_i⟩` block) is unchanged if the leg statements are kept as written.
`canonStageAt` changes them syntactically but not up to definitional unfolding of a same-file
abbreviation. The prototype will tell whether the consumer needs a one-line `show`.

**Plan if approved.** Build the two templates on legs 1 (move) and 0 (write) in scratch. If the
measured saving on those two is below 35 lines per leg, stop and report. Otherwise convert all
seven, then run the gate (152).
