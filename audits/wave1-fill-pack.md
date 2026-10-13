# External audit pack — wave-1 fill gate: R8.5c, the input length, and the §12.10 oracle-call layer (4 targets)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). Wave 1 added three
library layers whose statements were gated together and closed at round 2
(`audits/wave1-statements-r2-findings.md`; round 1 `audits/wave1-statements-findings.md`;
resolutions `audits/wave1-statements-resolutions.md`):
- **R8.5c** (`Build/InputLength.lean`, design §12.8b): a framed linear-time counter that writes
  `Nat.bits |x|`;
- **§12.10, the oracle-call simulation** (`Build/CertShell.lean`, `Build/OracleSim.lean`):
  - **W2-V**, the certificate shell;
  - **W2-C**, the choice-word machine, which removes nondeterminism from an oracle NDTM;
  - **W2-S**, the plain simulation of a polynomial-time oracle machine by a plain machine,
    given a plain decider for the oracle.

  These are the library rows behind `P^O = P` for `O ∈ P`, the `EXPCOM` summit and
  Baker–Gill–Solovay;
- the §12.8b record tables. They are **not** in this gate: two rows are in flight and four are
  paused (backlog MIG-23), and they get their own gate.

**This gate covers the four targets that are now proved:**

| Row | File | Target |
|---|---|---|
| R8.5c | `Build/InputLength.lean` | `Turing.exists_inputLengthTM` |
| W2-V | `Build/CertShell.lean` | `Turing.FinTM.exists_certificateShell` |
| W2-C | `Build/OracleSim.lean` | `Turing.FinOracleNDTM.exists_choiceTM` |
| W2-S | `Build/OracleSim.lean` | `Turing.FinOracleTM.exists_plain_simulation` |

Five deliveries were integrated, each by `git am -3` with Codex authorship. The statement gate's
head is `7d1e3947` (PR #43).

| Delivery | Brief | Agent commit (base) | Integrated | Result |
|---|---|---|---|---|
| R8.5c | `briefs/w1-fill-inputlength.md` | `27aab274` (`1e9361b5`) | `2b5b828d`, PR #54 (fills-4) | 1/1 |
| W2-V | `briefs/w2-fill-certshell.md` | `bb479e4b` (`1e9361b5`) | `ae4a8e79`, PR #54 | 1/1 |
| W2-C and W2-S | `briefs/w2-fill-oraclesim.md` | `5526e4d8` (`1e9361b5`) | `947fbdd7`, PR #54 | W2-C; W2-S partial |
| W2-S, continuation 1 | `briefs/w2-fill-oraclesim-cont.md` | `4737c0c1` (`ae9e0af5`) | `52f75eb0`, PR #59 (fills-5) | partial: 50 privates |
| W2-S, continuation 2 | `briefs/w2-fill-oraclesim-cont2.md` | `1ff39af0` (`3462c1b4`) | `a7644554`, PR #66 (fills-6) | **W2-S complete** |

One maintainer commit touches these files after the statement gate: `4a5b646b` corrects
`oracleHost`'s docstring, which still described W2-S as pending (comment-only).

**Every proof is kernel-checked.** The replay and axiom evidence is below, and all four targets
print within `[propext, Classical.choice, Quot.sound]`. Fill gates close on zero blockers and
zero majors (`workflow.md` §4). The duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in
force. The standards are attached.

**Bundle:** `audits/wave1-fill-bundle.md`: this pack, the standards, the statement-gate records, the briefs, the
reports, the integration records, the owned files with their bases, the patches, the freeze,
replay, axiom, screen and lint logs, and every screen-population file, so that the screen can
be rerun.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target bodies, `sorry` → proof** | the four targets |
| **Other publics** | none changed: every other public declaration of the three files, its docstring included, is byte-identical to the statement gate's |
| **Privates added** | `InputLength` 11, `CertShell` 20, `OracleSim` 87 (W2-C's and the first W2-S delivery's 17, then 50, then 20) |
| **Imports** | unchanged in all three files |
| **Docstrings** | flagged fill appendices on the targets, where a route was refined; the continuation appendices are kept as history |
| **Sizes** | `InputLength` 108 → 571 lines, `CertShell` 107 → 904, `OracleSim` 407 → 2,604 |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached bases (at `7d1e3947`), the heads and the
   cumulative patch (`audits/evidence/wave1-fill-gate/`):
   - every statement is unchanged, and so is every other declaration;
   - the only changed bodies are the four targets';
   - the imports are unchanged.
2. **R8.5c's route** (`briefs/w1-fill-inputlength.md`):
   - one framed counter for its own table, with **no counter proof copied** from Catalog's
     private `f2_counterTM` (note 44; the report measures the pair at 0%);
   - verdicts intercepted at each sub-module's exit; R1 isolation of the digit tapes; no
     termination hypothesis;
   - the work-space clause through the exit, with the exact finish restoring every head, the
     input position, the scratch and the output.
3. **W2-V's route** (`briefs/w2-fill-certshell.md`): built from public machine rows, citing the
   shared `append_split_unique` and `certificateLength_strictMono` (`ChoiceWords`) for the
   split. Its split-word term `certSplitWord` matches `Nondeterminism`'s private `contSplitWord`
   (100%) and `e3SplitWord` (90%). It is one four-line `match`, the output function of the
   public `FinTM.computesFunInTime_splitSolve`, and was pre-disclosed. **Backlog SH-1** retires
   the polynomial copy onto W2-V once this gate closes. Rule whether the pair is acceptable as
   pre-disclosed.
4. **W2-C's route** (`briefs/w2-fill-oraclesim.md`): states `N.State ⊕ Fin 3`; `N`'s ordinary
   tapes, the choice tape, then `N`'s query tape; lockstep in the `toOracleNDTM_runWith` shape; a
   blank choice cell emits `false` and halts. Per **minor 4**, at exhaustion in `N`'s query state
   the host may submit the query and discard the answer. **Note 50:** the exhaustion case is an
   executed example (`oraclesim-1-REPORT.md`, "Permanent execution sanity case").
5. **W2-S's route and its refinement.** The brief bound a dispatch host with a shadow tape, the
   install-mode clean call relocated by R1 and hosted by Z1 at the empty virtual input, and a
   scratch tape, with **nine R2-seamed phases** at `qQuery`. As delivered:
   - the finite host `oracleHost` is **one public phase host** (`phaseHostTM`), with a single R2
     seam between the public copy and the relocated call (`oracleService_run`), as documented in
     the target's appendices and the third report;
   - preparation (`oraclePrepare`) and restoration (`oracleRestore`, `oracleRestore_cut`) cost
     `natAbs p + 3` steps each, for both signs of the head's displacement and for zero, with an
     arbitrary original cell `-1`;
   - a query costs at most `2·|p| + 2·|z| + tCall + 13`, redirects included;
   - the global invariant (`oracleStableCfg`) and the time ledger.

   **Confirm** that the refinement is sound, that it is documented, and that it is no weaker than
   the bound route: the off-query transfer through `runFrom_eq_plainEmptyOracle` and Z5; the
   query bound from W2-0 (`queryString_runFrom_length_le_of_blank`); first-halt cuts by
   `MultiTapeTM.exists_first_halt`. Check that the oracle model's **time-only** decision holds
   (note 45: no space clause), and that the virtual input stays at the plain level.
6. **The corollaries.** `exists_plain_simulation_of_monotone`, `_initCfg` and `exists_plain_decider`
   (statement-phase derivations), together with the downstream `POracle_eq_P_of_mem_P`
   (`ClassOracle/Classes.lean`), now have empty admission walks. Confirm.
7. **Duplication** (failure mode 5):
   - Each delivery's screens are recorded (the reports and `audits/logs/*-screen-after.txt`). No
     delivery introduced an undisclosed cross-file pair involving its owned file.
   - **In-file families:**
     - continuation 1's eleven in-file pairs at 52–80% (the local-dispatch configuration and
       step lemmas of the prepare, restore and walk phases, each justified in its report);
     - continuation 2's two (`oracleHost_initial` against `oraclePrepare_tail` and
       `oraclePrepare_zero`, 51–52%).
   - **The gate's union screen** (`audits/logs/wave1-fill-gate-screen.txt`, 34 files at the
     head: 1,926 declarations, 2,364 pairs) adds `Simulation.lean`, which no wave-1 population
     held. No pair touching the three files is new against the earlier screens, the fills-6
     chapter-3/4 union included. It shows the **older pairs** that union first exposed:
     OracleSim's `oracleChoiceAction`, `oracleChoiceCfg` and `oracleShadowAction` against
     `Simulation.lean`'s `leftAction`, `rightAction` and `rightCfg` (53–75%), and
     `oracleBankCfg_eq` against Loop's `emCall_exit_fixed` (56%). They are recorded as backlog
     F6-1(i). **Rule** whether each is a copy to factor or a forced specialization. The
     maintainer's reading: the action and configuration definitions are short tape-layout
     terms written for a different bank (the oracle host's shadow and choice tapes).
   - All population files and the screen script are attached for a rerun.
8. **Promotion.** `oracleEmbed_updateTape` (OracleSim, private) is a generic embedding fact,
   recorded as F6-1(f) for MIG-16. Say whether it should be promoted before any other consumer.
9. **Documentation.** Check the appendices, status labels and every new private's docstring
   and sketch against the delivered proofs. One cosmetic linter suggestion stands in CertShell
   (`CertShell.lean:184`, `simpa` → `simp`).
10. **Size.** `OracleSim.lean` is 2,604 lines. The briefs waive size, and file size alone is not a
    driver (user, 2026-10-11). Say whether you disagree.
11. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** Every delivery's `SHA256SUMS` was all OK; the five manifests are
  attached. The deliveries' environment shims and agent scripts were never compiled or run, and
  nothing references them. These are maintainer attestations.
* **Freeze:** per delivery, `audits/logs/{w1-inputlength-fill-1,w2-certshell-fill-1,w2-oraclesim-fill-1,w2-oraclesim-fill-cont-1,w2-oraclesim-fill-cont-2}-freeze.log`;
  cumulative, `audits/evidence/wave1-fill-gate/freeze-cumulative.log`.
* **Replays** (user-run, fresh `.oleans` into tip-consistent snapshots): fills-4
  (`audits/logs/fills-4-replay.log` with two top-ups), fills-5 (`audits/logs/fills-5-replay.log`)
  and fills-6 (`audits/logs/fills-6-replay.log`, 41 modules), all with **0 errors**. In the last,
  `OracleSim`, `CertShell` and `InputLength` have no sorry warning.
* **Axioms** (`audits/logs/wave1-fill-gate-axioms.log`; probe
  `audits/evidence/wave1-fill-gate/AxW1Gate.lean.txt`, against the fills-6 replay tree):
  - every public of the three files and of `ClassOracle/Classes.lean`: 26 admission walks, all
    empty; 25 axiom prints, all within the standard three;
  - the censuses of every private constant (InputLength 120, CertShell 78, OracleSim 350,
    Classes 24) find no `sorryAx`.

  The fills-5 and fills-6 axiom logs are attached as well.
* **Lint** (`audits/logs/fills-6-stylelint.log`): 0 FAIL over `TuringMachine`; the warnings are
  all file-size ones.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/wave1-fill-findings.md`. The gate closes when it has zero blockers and zero majors.

## Erratum (gate round 1, minors F2–F5; `audits/wave1-fill-resolutions.md`)

- **Axioms.** "25 axiom prints" should read **26 axiom prints: 25 within the standard three, one
  (`FinTM.prefixWords`) with none**. There are also 26 admission walks, all empty.
- **Design extract.** `audits/evidence/wave1-fill-gate/design-12.8b-12.10.md` is **historical**: it
  predates the fills. Design §12.10 now gives the rows' proved status, W2-C's exhaustion
  exception, and W2-S's delivered phase-host refinement.
- **Earlier screens.** The comparison with the fills-6 combined screens is now checkable:
  `audits/logs/wave1-fill-gate-earlier-pairs.txt`.
- **Execution evidence.** The W2-S sanity probe and its log are attached, and the maintainer
  elaborated the probe (`audits/logs/wave1-fill-gate-sanity-maintainer.log`).
