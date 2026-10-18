# Ch3–4 fill campaign — wave-1 fill: §12.10 W2-V, the certificate shell (`Build/CertShell.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and its records (`audits/wave1-statements-*`);
  - R8.0b (`counterLoopTMVia`, PR #38) and R8.6 (`expandTM_run_ofCfg`), both proved;
  - the §12.8 Catalog Part 3, Scan, InputCall and Seam rows, all proved;
  - this round's order lists, base sorry sets, screen bases and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w2-certshell`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w2-certshell.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| R8.5c, the input length | `briefs/w1-fill-inputlength.md` | `TuringMachine/Build/InputLength.lean` |
| §12.8b record tables | `briefs/w1-fill-recordtable.md` | `TuringMachine/Build/RecordTable.lean` |
| §12.10 W2-S and W2-C | `briefs/w2-fill-oraclesim.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.10 W2-V | `briefs/w2-fill-certshell.md` | `TuringMachine/Build/CertShell.lean` |
| B5a, the code simulator | `briefs/b5a-fill.md` | `TuringMachine/CodeSimulator.lean`, `TuringMachine/Codes2Tape.lean`, `Diagonalization/EXPCOM.lean` |
| The ND code scheme | `briefs/ndcodes-fill.md` | `TuringMachine/NDCodes.lean` |
| B4a, the TQBF codec | `briefs/b4a-fill-codec.md` | `ClassPSPACE/TQBF.lean` (one target) |

Also in flight: §12.8 C continuation 3 (`Build/CfgRecord.lean`), B7 continuation 3
(`Logspace/QueryReshape.lean`, `Logspace/Reductions.lean`) and the B7 multiplication batch
(`Logspace/Mult.lean`); and a maintainer PR filling `POracle_eq_P_of_mem_P`
(`ClassOracle/Classes.lean`) and `baker_gill_solovay` (`Diagonalization/Relativization.lean`).
A parallel batch's work is invisible to your base and your screen.

## What this is

Fill **W2-V**, `FinTM.exists_certificateShell` (design §12.10; statement audited true at the
wave-1 statement gate): the plain shell that decides
`{x ++ u | |u| = C·(|x| + 1)^c ∧ out x u = [true]}` within `b·((m + 1)^e + T m)`, given a plain
machine that halts with output `out x u` from `Cfg.ofWords` with the certificate on a work tape.
With the proved `exists_proj_decider` and `certificateShell_proj` it decides the projected
language: the verifier side of [AB09, Claim 2.4 and Theorem 2.6], and the third step of the
choice-word route to B5's summit.

**Read first:** `Build/CertShell.lean` (the sketch is binding); design §12.10; the wave-1
findings and resolutions; `ClassNP/Nondeterminism.lean`'s private 2B shell
(`cont_choiceVerifier_mem_P`, the paired-input loader, `choiceCore`), which is your **template**;
`policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w3-preship.log`): 0 errors; its reuse census shows that the route's one formerly
sorried row, the native-input call R8.5e (`FinTM.exists_inputCallTM`), now prints `[]`.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/CertShell.lean:71` | `Turing.FinTM.exists_certificateShell` | R8.5e at `splitSolve`, then Z1 inside the returning R1 capture | — |

- **Owned:** `TuringMachine/Build/CertShell.lean`, for the target's body and new `private` declarations.
- **Not yours:** `Build/OracleSim.lean` (parallel batch), `ClassNP/Nondeterminism.lean` (closed and frozen: its private shell stays), and the facade.

### Proof route (binding; the docstring's sketch, amplified)

1. Install the split `pairEncode x u` of the input `y` (the empty word on failure, which rejects)
   on a work tape by the native-input clean call `FinTM.exists_inputCallTM` (R8.5e, proved) at
   `FinTM.computesFunInTime_splitSolve C c`.
2. Duplicate it (`copyTM_run_ofCfg`); install `x` and `u` by the install-mode clean calls of
   `FinTM.computesFunInTime_pairFst` and `computesFunInTime_pairSnd`; move them to the Z1 buffer
   and to bank tape `j` (`transferTM_run_ofCfg`).
3. Run `P` under Z1 from `vhostCfg (Cfg.ofWords P.q₀ (Function.update (fun _ => []) j u)) true 1 []`
   (the tag `true` is valid at position `1` for every `x`), inside the **returning** R1 capture
   `embedSilentRetTM` over `vhostEmitTM P` (`vhostEmitTM_runFrom`, `embedSilentRetTM_run`). The
   closed `vhostSilentTM` would die with `P`. It lands in its return anchor at `P`'s first halt
   with `P`'s output on the capture tape.
4. A three-state scan of the capture (first cell `true`, second blank) gives the verdict, which
   is emitted. Phases by R2 seams; time `c·(m + 1)^(c + 2) + O(m) + T m + O(T m + 1)`.

**The template is private.** Nondeterminism's 2B shell cannot be cited from here. Build the
shell from the public rows above with the core a parameter, and **never copy its proofs**.
Deduplicating that private shell against yours is a named 12.2c item (design §12.10, decision 3:
the shell's second customer); it is not yours.

## Gate guidance (binding)

- **Decisions (user, 2026-10-11).** One oracle-call trace (the deterministic row); nondeterminism
  by choice words, never a branchwise row; W2-S in preloaded generality (`initCfg` derived);
  **time only** — the oracle model has no space measure, so add no space clause (note 45).
- **Virtual input stays at the plain level**, after the simulation: an oracle-level Z1 would
  re-prove Z1's lockstep.
- **Mirrors, factored** (round 2): `certificateShell_proj` already cites the shared
  `append_split_unique` and `certificateLength_strictMono` (`ChoiceWords`); reuse them for any split.

## Cited infrastructure (public and proved at the issue commit)

- `FinTM.exists_inputCallTM` (InputCall, R8.5e), `FinTM.exists_installCallTM` (Loop),
  `FinTM.computesFunInTime_splitSolve`/`_pairFst`/`_pairSnd` (Primitives), `copyTM`/`transferTM`/
  `clearTM` (Catalog), `vhostEmitTM`, `vhostEmitTM_runFrom`, `vhostCfg` (Z1), `embedSilentRetTM`,
  `embedSilentRetTM_run` (R1′), R2 (Seam), `exists_first_halt`; `ChoiceWords`' five lemmas;
  `Complexity.exists_proj_decider`.
- **Proved modulo: none.**

## Ground rules (binding)

1. **File ownership.** Only `Build/CertShell.lean`. Change only the target's body, and add new `private` helpers
   there. List every new declaration with its role. A lemma that genuinely belongs in a shared
   file is written privately, flagged in `REPORT.md` as a promotion candidate, and promoted by
   the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your files' status text may change: the module's "Status" paragraph,
   its "Main results" tag, and your targets' "(statement)"/"(spec, fill pending …)" tags, each to
   "proved" (or to the new count, for a file you share with later targets); flag each. No new
   public declaration unless this brief names it.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
   it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report each owned
   file's final line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/w1-fill-screen-base.txt`:
**1,331 declarations, 1,717 pairs, 574,720 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/InputLength.lean \
  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean \
  TCSlib/Complexity/TuringMachine/Build/CertShell.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean \
  TCSlib/Complexity/TuringMachine/CodeSimulator.lean \
  TCSlib/Complexity/TuringMachine/ChoiceWords.lean \
  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/InputCall.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean \
  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean \
  TCSlib/Complexity/TuringMachine/Oracle.lean \
  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean \
  TCSlib/Complexity/ClassNP/Nondeterminism.lean \
  TCSlib/Complexity/TuringMachine/CodeFormat.lean \
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean \
  TCSlib/Complexity/TuringMachine/Build/Primitives.lean \
  TCSlib/Complexity/ClassP/DTIME.lean \
  TCSlib/Complexity/TuringMachine/Universal.lean \
  TCSlib/Complexity/TuringMachine/UniversalBlock.lean \
  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean \
  TCSlib/Complexity/TuringMachine/UniversalStartup.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - **pre-disclosed:** your shell against `Nondeterminism`'s private 2B shell (`cont_choiceVerifier_mem_P`, the loader, `choiceCore`). Measure and report every pair; the shared *arguments* must come from the public rows, so a proof pair at 90% or more is a copy to remove;
  - the split argument: cite `ChoiceWords` (round-2 factoring), never restate it;
  - the capture and verdict scan against B2b's private `b2b_trial_*` in `SpaceComplexity/Inclusions` (a different host; do not copy).
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/w1-fill.txt` (**55 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill.txt )
  ```

  **Base sorry-warning set, 28** (`audits/logs/w1-fill-base-sorries.txt`, one entry per declaration).
  Yours: `Build/CertShell` 1. Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**27** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `TuringMachine/NDCodes`: exists_effectiveNDMachineCode
- `TuringMachine/Build/InputLength`: exists_inputLengthTM
- `TuringMachine/Build/RecordTable`: joinFields_length, fieldOffset_length, joinFields_cfgRecord_length, cfgRecord_field_ne_nil, cfgRecord_init, recordValid_iff_exists_cfg, joinFields_recordTemplate_length, binDigits_posWidth_succ, TableWF.field_ne_nil, tableOffset_eq, tableOffset_length, TableAt.recordAt_take, tableRewindTM_run_ofCfg, exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation, FinOracleNDTM.exists_choiceTM
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] The measured pairs against `Nondeterminism`'s private shell, for the 12.2c item.

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare lifted positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well;
  `exists_installCallTM` gives it only for `0 < t`.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`, hence `posWidth`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `omega` with products and powers as atoms (`ring` first to expose them); `nlinarith` is
  rarely needed. The linter needs a literal "Proof sketch" before every `sorry` (partial only).
