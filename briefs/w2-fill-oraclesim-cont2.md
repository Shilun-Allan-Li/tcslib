# Ch3–4 fill campaign — wave-1 fill, continuation 2: §12.10 W2-S, the oracle-call simulation (`Build/OracleSim.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 13957bf73eb37763259be1fd01a5cca9bd03c21f HEAD`
  succeeds. That commit contains:
  - the previous continuations of this round's three batches and their reports (`audits/wave1-fill-agent-reports/{oraclesim,recordtable}-2-REPORT.md`, `audits/b5a-fill-agent-reports/cont-1-REPORT.md`), with the integration record `audits/fills-5-integration.md`;
  - the `exists_tableFindTM` universe fix (`Γ : Type`, user option (b), flagged in its docstring) and the 12.2c T2a export `Turing.embedEmitTM_tr`;
  - the B4 pre-issue promotion: twelve CNF-grammar publics in `Formulas/CNFEncoding.lean`, and `MultiTapeTM.spaceUsedByTape_le_card_Icc` moved from `Build/Zone.lean` to `Build/Catalog.lean` (same name and statement);
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont2.txt`), base sorry sets, screen bases and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w2-oraclesim-cont2`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w2-oraclesim-cont2.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| B4, TQBF membership | `briefs/ch34-b4-mem.md` | `ClassPSPACE/TQBF.lean`: `TQBF_mem_PSPACE` only |
| §12.10 W2-S, continuation 2 | `briefs/w2-fill-oraclesim-cont2.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation 2 | `briefs/w1-fill-recordtable-cont2.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, the canonizer | `briefs/b5a-fill-canon.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_polyCanonizer` and new privates in its gap |
| B5a, the uniform simulator H1 | `briefs/b5a-fill-h1.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_uniformSimulator` and new privates in its gap |

Also in flight (wave 5): S1b (`SpaceComplexity/ConfigGraph.lean`), which cites five record-table
rows; B3a (`SpaceComplexity/Constructible.lean`); and B5b (`Diagonalization/EXPCOM.lean`, by
declaration), which cites W2-S and B5a's two rows. A parallel batch's work is invisible to your
base and your screen.

## What this is

**A second continuation** (`workflow.md` §4) of **W2-S**, `FinOracleTM.exists_plain_simulation`:
from any preloaded start, a plain host reproduces an oracle machine's halting output, answering
each query by a clean call of a decider, within
`a·(t+1)² + a·Σ_{r<t} [query at r]·τ(|query_r|)`. `POracle_eq_P_of_mem_P` (filled modulo W2-S) and
B5's summit (B5b, in flight) wait on it.

The first continuation added **50 admission-free privates**: the R1-relocated frozen call; the
source/shadow transport (`oracleShadow_run`); the off-query transfer (`oracleOffQuery`, via R1,
Z5 and `runFrom_eq_plainEmptyOracle`); the complete local query preparation (`oraclePrepare`)
and restoration (`oracleRestore`, `oracleRestore_cut`), for both signs of the query head's
displacement, zero, and an arbitrary original cell `-1`; the specialized copy
(`oracleCopy_intoBlank`); and a candidate phase-host machine `oracleHost`. **What remains is the
composition:** the complete query-service seam, the global simulation invariant, and the time
ledger. There is no obstruction.

**Read first:** the first continuation's report (`audits/wave1-fill-agent-reports/oraclesim-2-REPORT.md`),
especially its "Continuation frontier for W2-S", which is written for you; the earlier briefs
`briefs/w2-fill-oraclesim-cont.md` and `briefs/w2-fill-oraclesim.md` (routes and gate guidance
still bind); design §12.10; `Build/OracleSim.lean` in full.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w1-fill-cont2-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/OracleSim.lean:1266` | `Turing.FinOracleTM.exists_plain_simulation` | the dispatch host (W2-S) | the inherited components |

- **Owned:** `TuringMachine/Build/OracleSim.lean`, for W2-S's body and new `private` declarations.
- **Frozen in your file:** W2-C's proof and its helpers; the four first-delivery W2-S components
  (`oracleInstallCall`, `oracleFrozenCall`, `oracleQueryWindow`, `oracleCost_sum`); and the first
  continuation's **proved** privates (`oracleShadow_run`, `oracleOffQuery`, `oraclePrepare`,
  `oracleRestore`, `oracleRestore_cut`, `oracleRelocatedCall`, `oracleCopy_intoBlank`,
  `oracleBankCfg_eq`, `oracleWalk_run`, and their lemmas). Cite them; never change them.
- **Revisable:** the candidate definitions not yet proved to meet the contract
  (`oracleHost`, `oracleHostTapes`, `oracleSourceBank`, `oracleCallBank`). You may revise them if the
  composition needs it. Every proved lemma that mentions them must still hold, or be re-proved in
  place. Report each change.
- **Not yours:** `Build/CertShell.lean` (W2-V, proved), `Oracle.lean`, `OracleNondeterministic.lean`,
  `Build/OracleCall.lean`, `ClassOracle/*`, and the facade.

### Proof routes (binding; the docstrings' sketches, amplified)

- **W2-S, the dispatch host.** Tapes: the source's `k + 1` tapes first; a **shadow tape** whose
  head mirrors the query head, with an origin marker written on the first step; the bank of the
  install-mode clean call `C := Turing.FinTM.exists_installCallTM D (fun z => [χ_O z]) τ hD`,
  hosted by Z1 at the **empty** virtual input (`vhostEmitTM_runFrom` with `y = []`) and relocated
  by R1; a scratch tape carrying the saved cell `-1` and the side bit across the seams.
  - (i) **Off `qQuery`**, one host step per source step: the host table agrees on simulated
    states with the shadowed transport of `M.tm.plainEmptyOracle`, so the bridge
    `OracleTM.runFrom_eq_plainEmptyOracle` and Z5 (`MultiTapeTM.runFrom_eq_of_agreeOn`) carry
    `M`'s run.
  - (ii) **At `qQuery`**, nine R2-seamed phases (`seamCompTM_run_ofCfg`, `seamReleaseTM`):
    bookmark the shadow cell; walk to the origin by the side; save and blank cell `-1`; copy the
    delimited query to `C`'s argument tape (`copyTM_run_ofCfg`, `OracleTM.queryString_eq_of_cells`);
    run `C`; read and clear the verdict; restore cell `-1`; walk back and erase the bookmark;
    enter the embedded `M.qYes`/`M.qNo` (`OracleTM.step_of_qQuery`).
  - (iii) **Ledger:** from a blank query tape the query at step `r` has length at most `r`
    (W2-0, `OracleTM.queryString_runFrom_length_le_of_blank`), the query head is within `r` of
    the origin, each query costs `a·(t + 1) + a·τ |z|`, and there are at most `t` of them. The
    host halts exactly when `M` does; first-halt cuts by `MultiTapeTM.exists_first_halt`.

### The frontier you inherit (the first continuation's; resume at step 1)

1. Instantiate `oracleInstallCall D O τ hD` once, and specialize `oracleHost` to its `C`, entry
   and exit. `oracleRelocatedCall` supplies the Z1/R1 return and the complete earlier-exit cut;
   no new clean-call or virtual-input trace is needed.
2. Define the stable full-host configuration: the first source bank tracking the source run, the
   origin shadow, the clean-call/virtual-input bank and blank scratch. Prove the two
   initialization handovers from the requested `prefixWords` preload, identifying the local R1
   views by `oracleBankCfg_eq`.
3. Connect `oraclePrepare` through the dispatch R1 embedding and the phase-host guard. Apply the
   frozen `oracleQueryWindow` at the left-blanked source tape, then `oracleCopy_intoBlank`, and
   identify the result with `oracleRelocatedCall`'s input seam. Compose the service by the public
   `seamCompTM_run_ofCfg` and its first-return contract, accounting the host's redirect steps
   explicitly.
4. Connect the singleton-verdict return to `oracleRestore` and `oracleRestore_cut`. Prove the
   complete full-host seam into the source's `qYes`/`qNo` (`OracleTM.step_of_qQuery`), with every
   ambient tape and head, the native input and the accumulated output.
5. Establish the candidate host's agreement off the query table, as `oracleOffQuery` needs, and
   prove the global simulation invariant by alternating off-query segments and complete query
   seams.
6. Use the existing public query-radius and length rows at source time `r`. Bound preparation,
   copy, call, restoration and redirects by a fixed multiple of `r + 1` plus the actual `τ |z|`
   charge, apply `oracleCost_sum`, absorb initialization, and finish with `exists_first_halt`.
   No monotonicity of `τ` may be introduced.

## Gate guidance (binding)

- **Decisions (user, 2026-10-11).** One oracle-call trace (the deterministic row); nondeterminism
  by choice words, never a branchwise row; W2-S in preloaded generality (`initCfg` derived);
  **time only** — the oracle model has no space measure, so add no space clause (note 45).
- **Virtual input stays at the plain level**, after the simulation: an oracle-level Z1 would
  re-prove Z1's lockstep.
- **Note 50:** permanent sanity case **at fill**: query-word exhaustion for W2-C, as an
  executed example in your evidence.
- **Mirrors, factored** (user decision, round 2): W2-0 and the oracle run invariants already
  specialize the public `OracleTM.step_radius`/`runFrom_radius`; cite them, never restate them.

## Cited infrastructure (public and proved at the issue commit)

- `Oracle.lean`: the run algebra, `step_of_qQuery`, `step_eq_of_ne_qQuery`, `queryString_eq_of_cells`,
  `runFrom_eq_plainEmptyOracle`, `step_radius`, `runFrom_radius`; `OracleNondeterministic.lean`:
  `toOracleNDTM_runWith`, `stepWith`, `fixChoice`; `Build/OracleCall.lean`: `answerAction` and the
  query tail.
- `FinTM.exists_installCallTM` (Loop), `vhostEmitTM`, `vhostEmitTM_runFrom` (Z1), R1 and R2
  (Embed, Seam), `copyTM_run_ofCfg`, `clearTM_run_ofCfg` (Catalog), `MultiTapeTM.runFrom_eq_of_agreeOn`,
  `exists_first_halt`, `FinTM.prefixWords` and its lemmas, `Cfg.init_eq_ofWords`, W2-0.
- **Proved modulo: none.**

## Ground rules (binding)

1. **File ownership.** Only `Build/OracleSim.lean`. Change only W2-S's body, and add new `private` helpers there. List every new declaration with its role. A lemma that genuinely belongs in a shared
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
**Duplication**). The base, at this brief's issue tree, is `audits/logs/w1-fill-cont2-screen-base.txt`:
**1,477 declarations, 1,747 pairs, 582,620 characters**.

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
  - the first continuation's 50 privates: cite them; never write a second walk, copy or restoration trace;
  - the four inherited components: cite them; the first delivery's two in-file pairs (60%, 56%) are recorded;
  - a second oracle-call trace, a branchwise simulation, or an oracle-level Z1 (decisions above);
  - the off-query lockstep against Z5 and the bridge: cite them;
  - the query extraction against `Build/OracleCall`'s capture and B1's private oracle helpers (`ClassOracle/*`): never copy them;
  - W2-C's induction against `toOracleNDTM_runWith`'s: cite its shape, do not restate it.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/w1-fill-cont2.txt` (**88 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill-cont2.txt )
  ```

  **Base sorry-warning set, 18** (`audits/logs/w1-fill-cont2-base-sorries.txt`, one entry per declaration).
  Yours: `Build/OracleSim` 1 (`exists_plain_simulation`). Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**17** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `Diagonalization/EXPCOM`: NPOracle_EXPCOM_subset_EXP
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM
- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.

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
- `OracleTM.runFrom` takes the oracle `O` explicitly; a plain machine's `runFrom` does not.
  The bridge `runFrom_eq_plainEmptyOracle` is the link off `qQuery`.
- Oracle answers are classical: use `simp only [this, decide_eq_true_eq]`; `rw` fails inside
  `ite` (motive not type correct).
