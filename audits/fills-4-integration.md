# Ten fill deliveries (seven complete, three partial): integration record

Side branch `integrate/fills-4`. Each delivery was applied by `git am -3`, keeping its Codex
authorship, at the campaign tip. Its owned files were unchanged between the agent's base and the
tip, and each matches the delivered snapshot byte for byte.

| Delivery | Brief | Agent commit (base) | Integrated | Report |
|---|---|---|---|---|
| §12.8 C, continuation 3 | `briefs/s128-fill-C-cont3.md` | `35fa0071` (`635afc66`) | `14d1a383` | `audits/s12-8-fill-agent-reports/C-cont-3-REPORT.md` |
| B7, continuation 3 | `briefs/ch34-b7-cont3.md` | `fe9b6ee3` (`0bf08187`) | `9ce4c35a` | `audits/b7-fill-agent-reports/fill-4-REPORT.md` |
| B7, multiplication | `briefs/ch34-b7-mult.md` | `e685dd85` (`0bf08187`) | `f521bfbc` | `audits/b7-fill-agent-reports/fill-5-REPORT.md` |
| The ND code scheme | `briefs/ndcodes-fill.md` | `152e9c4d` (`1e9361b5`) | `c7e42483` | `audits/ndcodes-fill-agent-reports/REPORT.md` |
| R8.5c, the input length | `briefs/w1-fill-inputlength.md` | `27aab274` (`1e9361b5`) | `2b5b828d` | `audits/wave1-fill-agent-reports/inputlength-1-REPORT.md` |
| §12.10 W2-S and W2-C (partial) | `briefs/w2-fill-oraclesim.md` | `5526e4d8` (`1e9361b5`) | `947fbdd7` | `audits/wave1-fill-agent-reports/oraclesim-1-REPORT.md` |
| §12.8b record tables (partial) | `briefs/w1-fill-recordtable.md` | `bde2e9c1` (`1e9361b5`) | `9e375aad` | `audits/wave1-fill-agent-reports/recordtable-1-REPORT.md` |
| §12.10 W2-V, the certificate shell | `briefs/w2-fill-certshell.md` | `bb479e4b` (`1e9361b5`) | `ae4a8e79` | `audits/wave1-fill-agent-reports/certshell-1-REPORT.md` |
| B5a (partial) | `briefs/b5a-fill.md` | `a2914d4c` (`1e9361b5`) | `b13425cb` | `audits/b5a-fill-agent-reports/REPORT.md` |
| B4a, the TQBF codec | `briefs/b4a-fill-codec.md` | `f5449004` (`1e9361b5`) | `7b3c4747` | `audits/b4a-fill-agent-reports/REPORT.md` |

## Results

- **§12.8 C: `Turing.exists_recordStepTM` is proved (7/7).** The live-source branch composes the
  full native cycle, including the empty input, complement, normal-branch borrow, saved-position
  seek and D cleanup. It restores the native position and output exactly. It rejects an outward
  move before any record write, and otherwise rewrites the fixed-length record field by field.
  The common coefficient `200·(k + 3)·(Cseek + 1)` stands. There are 12 new privates: 11
  theorems and one abbreviation. There is no new host, restriction lemma or hand table. **§12.8
  streams A–C are complete: 24/24.**
- **B7 targets 9–11 are proved.** `compQ` (N4) is one mode-parametrized ARM over the four-oracle
  bank. It validates the inner field canonical without decoding it, finds `F` by a capped
  lifted-length search, and has the register bound `8·(2C + 3)·(n + 1)^(e + 1)`. `comp` and
  `trans` are the prescribed corollaries. There are 55 privates in `QueryReshape` and one in
  `Reductions`.
- **B7 target 12 is proved:** `multLang_mem_LOGSPACE`, by an ARM over the access bank, with the
  column/carry invariant **proved** (gate note 12) and bounded halting on every input. There are
  62 privates. **B7 is complete: 12/12.**
- **The ND code scheme is proved:** `exists_effectiveNDMachineCode`, as the third `CodeFormat`
  instance (one private `ndFormat`), with the sanctioned `MathlibBridge` import. The canonizer is
  arbitrary-time, as audited.
- **R8.5c is proved:** `exists_inputLengthTM`, by a one-tape, six-state framed counter
  (`C = 6`), whose input return reuses `inputFoldTM`'s backward transition with
  `FinTM.rewind_heads`; 11 privates. Note 44 is met: the measured pairs against Catalog's private
  `f2_counterTM` family are 0–13%, recorded for 12.2c.
- **W2: partial, 1/2.** W2-C (`FinOracleNDTM.exists_choiceTM`) is proved, by lockstep over the
  choice suffix, with the note-50 exhaustion sanity case executed. W2-S keeps its original
  `sorry`; four of its components are proved (`oracleInstallCall`, `oracleFrozenCall`,
  `oracleQueryWindow`, `oracleCost_sum`). There are 17 privates. A continuation brief issues with
  this PR.
- **Record tables: partial, 13/20.** The twelve layout and table facts and the adapter
  `tableRewindTM_run_ofCfg` are proved. So is the copier `rt_copyMachine`, with its zero- and
  one-field contracts. Rows 14–20 keep their `sorry`s. There are nine privates and one flagged
  Mathlib import (`Mathlib.Data.Nat.Bitwise`, for `Nat.testBit_eq_inth`; rule 6 permits it).
  A continuation brief issues with this PR; R8.5c being proved leaves it no proved-modulo row.
- **W2-V is proved:** `FinTM.exists_certificateShell`, with no proved-modulo dependency. A
  native-input clean call computes the `splitSolve` word. A one-step guard rejects the empty
  failure value before any simulation. The paired loader installs both components through the
  public `pairFst`/`pairSnd` install calls, and the source runs under `vhostEmitTM` inside the
  returning R1 capture. A three-state controller reads the captured output backwards and tests
  it equals `[true]`. The language equivalence cites `ChoiceWords`' split uniqueness. The
  coefficient is `b·(A + 3) + a + 8` at degree `c + 2`. There are 20 privates, five of them
  flagged promotion candidates (`Build/Embed`, `Build/Seam`, the §12.2c shell deduplication).
- **B5a: partial, 6/8.** Targets 3–8 are filled:
  - both scheme instances: `exists_uniformMachineCode2` at a private two-tape format, and
    `exists_uniformMachineCode` by route Z at `oneTapeMachineFormat`;
  - the padding reduction `EXP_subset_POracle_EXPCOM`, with no per-code simulator constant;
  - the three `EXPCOM` identities.

  All six are **proved modulo** the two §12.11 rows, and 6–8 also modulo B5's summit (D5
  permits this). Targets 5–8 reach the rows through the language `EXPCOM` itself
  (`expCode := Classical.choice exists_uniformMachineCode`). The two rows,
  `MachineFormat.exists_polyCanonizer` and `exists_uniformSimulator`, keep their original
  `sorry`s. Their semantic preparation is proved:
  - the canonizer's positive grammar guard (sound when `F.guard = 0`, minor 5),
    `guardedScan_eq`, the fallback identity `decode_of_grammar_guard`, and the state-count bound;
  - the D4 output summary and semantic clock, generalized to `k` tapes
    (`summaryClock_accepts`).

  The D4 ledger is 7 moves and 9 deletions, with `zfBFallback_serialize_length` kept. Note
  50's two sanity cases were executed on the semantic layer only. A continuation brief issues
  with this PR (`briefs/b5a-fill-cont.md`).
- **B4a is proved:** `exists_adjacency_codec_cnf`, admission-free. The configuration codec
  factors through the public `ConfigCount.coreCode`, carrying the input and output summary
  separately. Validity, adjacency and acceptance are three CNFs. Adjacency is a family of
  fixed-arity gates (`3k + 7` ports), each built by `exists_cnf_boolFun`, never a whole-row
  truth table. Output normalization cites `NDTM.coreSum_stepWith`. The CNF ledger counts
  literals plus one per clause. There are 119 privates, six of them flagged promotion
  families. The three TQBF summit rows are untouched.
- No escalation, no admitted helper and no machine correction in any of the ten. The only
  proved-modulo citations are B5a's, all sanctioned by its brief.

## Verification (maintainer)

- **Integrity.** All `SHA256SUMS` entries were OK: 25, 30, 22, 22, 30, 34, 33, 40, 63 and 28. Each
  git bundle verifies against the campaign history, and its tip equals the delivered snapshots.
  The deliveries' environment shims are excluded: `app-path.c` ×4, `lean-self-path.c`,
  `lean-proc-self.c`, `proc_self_compat.c`, `lean-self-exe.c`, `self-exe.c` and `selfpath.c`. So are the agent
  scripts: `freeze-audit.py`, `verify-evidence.py`, `scope_check.py`, `screen-owned.py`,
  `screen.sh`, `screen-owned.sh`, `lean-launcher.sh`, `freeze-check.py`, `analyze-screen.py`,
  `check-freeze.py`, `check-sorry-inventory.py`, `copy-coverage.py` and `lean-wrapper.sh`. None was compiled or
  run, and no patch references any of them.
- **Freeze** (`audits/logs/{s12-8-fill-C-cont-3,b7-fill-4,b7-fill-5,ndcodes-fill,w1-inputlength-fill-1,w2-oraclesim-fill-1,w1-recordtable-fill-1,w2-certshell-fill-1,b5a-fill-1,b4a-fill-1}-freeze.log`).
  - No statement changed and no public was added or removed.
  - Only the targets' bodies changed (authorized), plus the flagged status text and appendices.
  - Privates added: `CfgRecord` 12, `QueryReshape` 55, `Reductions` 1, `Mult` 62, `NDCodes` 1,
    `InputLength` 11, `OracleSim` 17, `RecordTable` 9, `CertShell` 20, `CodeSimulator` 17,
    `Codes2Tape` 2, `EXPCOM` 1 and `TQBF` 119. No existing private changed.
  - B5a's D4 removed 16 `Codes2Tape` privates, exactly its ledger. The freeze tool's one
    "public removed" is a false positive: a docstring line of the deleted
    `zfB3_uniform_of_simulator`. `certificateShell_proj` is byte-identical.
  - Imports are unchanged, except for three sanctioned additions and one flagged one. The
    sanctioned ones are NDCodes' `MathlibBridge` and B5a's two `CodeSimulator` imports (in
    `Codes2Tape` and `EXPCOM`). The flagged one is `RecordTable`'s `Mathlib.Data.Nat.Bitwise`.
    The combined import graph (577 modules) is acyclic.
  - The partials' open targets keep their original `sorry` lines. On those targets only the
    docstrings changed, by flagged partial appendices; for B5a's two this was checked on the
    comment-stripped code.
  - No forbidden token among the added lines.
- **Duplication.** Every screen matches its agent's byte for byte:
  - C, ordinary and with `Primitives`: 702 → 712 and 1,376 → 1,386 pairs;
  - B7 continuation 3 and the multiplication batch, each against the same 22-file base:
    72 → 75 each;
  - ND: 82 → 82;
  - the four wave-1 batches, each against the 24-file base at the tip (1,331 declarations,
    1,717 pairs), on a tree holding only its own file: R8.5c 1,717 → 1,717, W2 → 1,719
    (two in-file pairs, 56–60%), record tables → 1,724 (seven in-file pairs, 55–73%, the
    copier's state-family dictionaries), W2-V → 1,721 (the four pre-disclosed split-word
    measurements below);
  - B5a against its 27-file base (1,420 declarations, 1,769 pairs): 1,766 pairs. That is the
    two pre-disclosed mirror measurements, with five pairs gone through D4;
  - B4a against its 12-file base (758 declarations, 358 pairs): 363 (five in-file pairs, 51–74%).

  **Outside the pre-disclosed pairs, every new pair is in-file and below 90%**, each justified
  in its report. The pre-disclosed pairs are these:
  - **W2-V's split word:** `CertShell.lean::certSplitWord` matches `Nondeterminism`'s private
    `contSplitWord` at 74/74 (100%) and `e3SplitWord` at 64/71 (90%). This is one four-line
    `match` term, the output function of the public row `FinTM.computesFunInTime_splitSolve`.
    No public word-valued definition exists to cite. It is a definition, not a proof: 74 of the
    file's 19,659 extracted body characters. Its retirement is the shell deduplication against
    `Nondeterminism`'s private 2B shell, the 12.2c item named in design §12.10, decision 3, and
    now tracked as `backlog.md` SH-1. It is flagged for the wave-1 fill gate.
  - **B5a's mirror pair** (75%): backlog CH34-D3, below.

  **The batches screened together at the head.** These are
  `audits/logs/fills-4-wave1-screen-combined.txt` (24 files, 1,416 declarations, 1,735 pairs)
  and `audits/logs/fills-4-b5a-screen-combined.txt` (27 files, 1,511 declarations, 1,789
  pairs). Their only pairs beyond the per-batch screens are §12.8 C continuation 3's own ten
  in-file pairs, since the wave-1 base predates it. They add **no cross-batch pair**.

  **The two parallel B7 batches, screened together** (`audits/logs/b7-fills-45-screen-combined.txt`), give 72 → 79
  pairs: the six in-file pairs plus **one cross-batch pair**. `Mult.lean::mult_addresses`
  reproduces `QueryReshape.lean::comp_suffix_address` at 55%. Both apply the public
  `pairEncode_getD` lookup law to different nested layouts (`pairEncode a (pairEncode b c)`
  against `pairEncode (pairEncode x b) tail`). The maintainer classifies this as idiom, since
  the shared argument is already public, and flags it for the B7 fill gate. **New copies: none,
  beyond the two pre-disclosed pairs above.**
- **Lint** (`audits/logs/fills-4-stylelint.log`, `ndcodes-fill-stylelint.log`,
  `w1-fill-1-stylelint.log`, `fills-4b-stylelint.log`, `b4a-fill-stylelint.log`): 0 FAIL over
  `TuringMachine/Build`, `SpaceComplexity`, `TuringMachine`, `Diagonalization` and `ClassPSPACE`. The warnings
  are all file-size ones. CertShell's elaboration carries one cosmetic linter suggestion
  (`CertShell.lean:184`, `simpa` → `simp`), noted for the wave-1 fill gate.
- **Sizes:** `CfgRecord` 3,786 → 5,255; `QueryReshape` 1,208 → 2,621; `Reductions` 153 → 184;
  `Mult` 74 → 1,463; `NDCodes` 182 → 270; `InputLength` 108 → 571; `OracleSim` 407 → 842;
  `RecordTable` 779 → 1,237; `CertShell` 107 → 904; `CodeSimulator` 251 → 488; `Codes2Tape`
  550 → 330; `EXPCOM` 282 → 382; `TQBF` 285 → 1,902. The briefs waive size.
- **Replay** (user-run; `audits/logs/fills-4-replay.log`). The four changed C and B7 files' downstream
  closure, 11 modules, together, at `b0e922ab`: **0 errors.** `CfgRecord`, `QueryReshape`,
  `Reductions` and `Mult` have 0 sorry warnings; the rest are the out-of-scope `TQBF` 4,
  `Path` 2, `ImmermanSzelepcsenyi` 3 and `RecordTable` 20.
  **The top-up** (`audits/logs/fills-4-replay-topup.log`, user-run, at `b13425cb`) covered the
  downstream closure of the ten files changed since: the maintainer corollary fill (PR #53)
  and the six later deliveries. That is 15 modules, fresh `.oleans` into the same snapshot:
  **0 errors**. The sorry warnings are exactly the expected base: `OracleSim` 1,
  `CodeSimulator` 2, `EXPCOM` 1 (the summit), `NTimeHierarchy` 6, `RecordTable` 7, and 0
  elsewhere, including `Classes`, `Relativization`, `NDCodes`, `InputLength`, `CertShell` and
  `Codes2Tape`. **A second top-up** (`audits/logs/fills-4-replay-topup2.log`, user-run, at
  `7b3c4747`) covered B4a's downstream closure: `TQBF` and the `ClassPSPACE` facade, 2
  modules, **0 errors**. `TQBF` keeps exactly its three out-of-scope summit warnings.
- **Axioms and admission walks** (read-only against the replay tree).
  - `audits/logs/s12-8-fill-C-cont-3-axioms.log`: all 15 `CfgRecord` publics print within
    `[propext, Classical.choice, Quot.sound]`; the three record rows' walks are empty; none of
    the 1,059 private constants uses `sorryAx`.
  - `audits/logs/b7-fills-45-axioms.log`: all 51 publics of the five Logspace files print
    within the standard triple; **all twelve B7 targets' walks are empty**; the five censuses
    (365, 80, 1,182, 3 and 500 private constants) find no `sorryAx`.
  - `audits/logs/fills-4b-axioms.log` (probe `audits/evidence/fills-4/AxF4b.lean.txt`, against
    the top-up tree). It covers all 84 publics of the eight files of the six later deliveries,
    plus the two corollary targets, each with its admission walk:
    - NDCodes (7), InputLength (1), W2-C and W2-V print within the standard triple, and their
      walks are empty.
    - W2-S's walk is itself; its three public corollaries rest on W2-S alone.
    - In the record tables, the 13 proved targets and the 8 other publics have empty walks;
      each of the 7 open rows rests on itself alone.
    - B5a: targets 3–5 rest exactly on `exists_polyCanonizer` and `exists_uniformSimulator`.
      So do the definitions `expCode` and `EXPCOM`: the language rests on the scheme. Targets
      6–8 rest on those two rows and the summit `NPOracle_EXPCOM_subset_EXP`, and the summit
      itself also reaches the two rows through `EXPCOM`.
    - `POracle_eq_P_of_mem_P` rests on W2-S alone. `baker_gill_solovay` rests on the summit
      and the two §12.11 rows, now that the `EXPCOM` identities are filled.
    - The private-constant censuses find no `sorryAx`: NDCodes 14, InputLength 120, OracleSim
      43, RecordTable 52, CertShell 78, CodeSimulator 62, Codes2Tape 24, EXPCOM 6.
  - `audits/logs/b4a-fill-axioms.log` (probe `audits/evidence/fills-4/AxB4a.lean.txt`):
    `exists_adjacency_codec_cnf` and the file's four other non-summit publics print within the
    standard triple, and their walks are empty. Each of the three summit rows rests on itself
    alone. None of the 371 private constants uses `sorryAx`.
- **The B8 gate's comment-only sweep** (`b0e922ab`) is on the same branch; see
  `audits/b8-fill-resolutions.md`.

## Disposition

All ten go in by PR, with **two fill-gate packs** and **three continuation briefs**
(`briefs/w2-fill-oraclesim-cont.md`, `briefs/w1-fill-recordtable-cont.md`,
`briefs/b5a-fill-cont.md`). The packs are:
- **§12.8 A–C** (`audits/s12-8-fill-AC-pack.md`), over six deliveries;
- **B7** (`audits/b7-fill-pack.md`), over five.

The ND scheme joins the next gate that covers chapter-3 code schemes. B4a joins the B4 fill gate
with the TQBF summit batch, to which its file passes. R8.5c, W2-C, W2-V and the
record tables join the wave-1 fill gate when W2-S and the last record-table rows close. B5a goes
to its own fill gate when its two rows close; that gate cannot close over the human-review item
**CH34-D3**, opened in `backlog.md` §1 by this PR. That item covers B5a's pre-disclosed mirror
pair, which adds a copy to `Codes2Tape.lean`, a file that took copies in an earlier epoch
(`workflow.md` §4).
