# External audit pack — the ARM extensions (received code), round 2: the classified ledger, the host registry, the corrections

Round 2 of the fill-style gate of Hydroxyi's merge `8c23f3bc`. Round 1
(`audits/arm-extensions-fill-findings.md`, attached verbatim): **gate open, 0 blockers, 5 majors,
9 minors**. No frozen statement changed and no interface was found false. The five majors are about
duplication (findings 1–4) and the host policy (finding 5). The round-1 pack and bundle are
immutable; this pack supplements them. The gate closes on a round with **zero blockers and zero
majors**; a duplication major closes only by the user's explicit acknowledgement, recorded with its
named payback. Record findings in `audits/arm-extensions-fill-r2-findings.md`.

In this pack `r2/` is `audits/evidence/arm-fill/r2/`, and "the X log" is
`audits/logs/arm-fill-r2-X.log`.

**What did not change** (MEASURED, provenance log). The 81 received `.lean` files are
byte-identical at the received commit `8c23f3bc`, at the replay revision `733c22b7` and at the tip
`e831b5b0` (`e831b5b0d887dac3bbf1aa2c19af28983b15b982`). The tip's Lean tree is identical to that
of `39bfdca4` (round 1's findings commit), on which every round-2 script ran read-only. The copy
screen rerun over the 73 added files at the tip reproduces round 1's added-only output **byte for
byte** (772 declarations, 343 directed pairs; screen-added-only log). Round 1's `ledger.py`, rerun on
round 1's inputs, reproduces round 1's ledger byte for byte (ledger log).

**What changed underneath** (MEASURED). Since round 1's pack tip `dc891632` the campaign merged C1's
host contracts (#87), the chapter-7 citations (#89), MIG-0b's split (#90) and the StepBlock
sketches (#91). The changes of #89 (17 `.lean` files) and #91 (one) are comment-only
(comment-only log). The tip records the user's dedup decisions (backlog §1 ARM-1 and ARM-2 at
`e831b5b0`). Open, not merged when this pack was built: **#92** (the B6 hosts) and **#93** (the
maintainer's ARM minor fixes: findings 6, 10 and 11); both have since merged (maintainer note
below). Of the 214 files of round 1's screen population, 202 are
byte-identical at the tip, 3 differ in comments only and 9 in code (C1: `Nondeterministic`,
`NondeterministicSpace`; MIG-0b: `Build/{Catalog,CfgRecord,CounterLoop,Embed,Seam}`, `Finite`,
`StateRenaming`). Only two ledger pairs touch a changed file, both incidental; their library lines
moved (`Catalog` 6255→6235, `Embed` 743→750). Everything else cited here has the same lines at the
received tree and the tip (drift log).

**Maintainer note, after the pack was built (2026-10-14).** #92 and #93 are now merged; the
campaign tip is `3a6e89f4fc2319f708a0ab580d7bc0631d4a9ce3` (Lean content as `1b6b972c`, the merge
of both).
- **Every `TCSlib/` file in the bundle is at `e831b5b0`**, the base this ledger was measured on.
  That keeps every count and `file:line` here reproducible.
- **#93** changed comments and imports only, in 33 of the 73 added files; its diff is bundled
  (`r2/pr93.diff`).
- **#92** changed three bundled library files: `ConfigGraph` (the originals of D1–D3 and D5;
  four `s1b_*` declarations moved and seven private copies removed), `ConfigCount` and
  `Build/CfgRecord`. Their lines here are at `e831b5b0`; the payback PR re-measures them at its
  base.
- **Checked by the maintainer at the tip:** ConfigGraph's remaining private `s1b_*` block, 11
  declarations, has no consumer, so it stays slated for deletion in the payback PR.
- **Every other bundled file** (the records, the evidence) is at the maintainer's records commit
  that lands this round.

## The user's decisions (binding, 2026-10-14)

From round 1's close:
1. **Recount first, then acknowledge.** The builder produces the complete classified ledger; the
   user then acknowledges its whole scope once, in this round. The acknowledgement is the user's;
   this pack leaves its place (below) and does not record it.
2. **Owner of the deduplication:** the user's own refactor window (maintainer-owned), coordinated
   with Hydroxyi because it edits his files; Hydroxyi keeps correctness. The payback PR after the
   B6 hosts stays, gated.
3. **Host policy:** the received machinery is registered in `machine-library-design.md` §14 with
   public contracts, consumers, resource clauses and intended generic forms. Today's first uses
   are an accepted exception; a contract gate is required before any further consumer is briefed.
4. **The minor fixes in the new files** are made by the maintainer in one PR: **#93, merged on
   2026-10-14** (findings 6, 10, 11; replay 74 of 74).

The dedup decisions (backlog §1 ARM-1, "Dedup decisions", and §1 ARM-2, at `e831b5b0`):
- **(1) The payback PR after the B6 hosts** (owner: maintainer; a full gate, since D1 changes
  public statements):
  - **D1:** standardize on the public `Turing.Cfg.InWindow` (`Build/CfgRecord.lean:100`); delete
    ConfigGraph's private `InWindow`, its bridge `inWindow_iff_cfgInWindow`, and Codec's `InWin`.
    `InWin`'s 48 code uses in 7 files change (MEASURED, records log);
  - **D2, D2h, D3, D5:** promote ConfigGraph's originals, stated with `Cfg.InWindow`; delete the
    copies in `Codec/Bridge` and `ExpBFS/Radius`; delete ConfigGraph's dead `s1b_*` block;
  - **D4:** promote DAGCircuitSat's Tseitin lemma, delete `TQBFHardTseitin`'s copy (cleared with
    Hydroxyi);
  - **D6:** delete our dead private `b4m*` appendix of `TQBF.lean` (lines 2474–3185);
    `TQBFARM/Semantics`' public twins stay;
  - **D7 and `decChain`:** one parameterized stride decoder in `Logspace/InputAccess`, with
    `Codec/Engine`'s as instances;
  - **`length_lbStep`:** share a helper with `PolyTimeBlockLoop.length_xorPairStep_le`.

  "The ARM gate's round-2 ledger may add rows to this list."
- **(2) ARM-2, "to coordinate with Hydroxyi", not scheduled:** (a) the re-derivations of his
  earlier `Machines/` library, (b) the duplication inside the new files (internal families and
  same-file pairs). A shared-interface design, coordinated before any brief, then a PR plus its
  gate under the zone rules.

From this round's ledger (the user, 2026-10-14, after reading the ledger summary):
5. **The acknowledgement** of the complete classified ledger is recorded below
   ("Acknowledgement").
6. **The proposed payback rows join the payback PR:** the 15 P1+ pairs (13 declarations, with
   `toCNF_extension_iff` riding with D4) and the manual row M2 (`VWord.getD_drop`).
7. **Finding 12's other helper moves go to ARM-2** (`Path.getD_flatMap_rows` is already in
   ARM-2 (a); `NARMProof.NSPACE.mono_const`, `ARMWidth`'s class facts and the `ExpBFS` namespace
   split join it).

Maintainer, recorded with these: the registry rows are numbered H7–H13 as drafted; ARM-1's count
of the dead `b4m*` appendix is corrected to **45** declarations (this pack's count; the line
range was right).

## Resolutions, finding by finding

1. **Finding 1 (major), the disclosed debt.** Every disclosed family now has a decided resolution
   in the payback PR, D6 and D7 included (above). The 18 disclosed declarations are ledger rows of
   group P1. Closure: the user's acknowledgement (below).
2. **Finding 2 (major), the twelve undisclosed substantive copies.** Each is a ledger row with its
   source counterpart, shared characters, what is shared, the contract that would remove it, and
   its group (table in "The ledger", below): 2 in the payback PR (`decChain`, `length_lbStep`), 10
   in ARM-2. The delivery report's omission stays recorded as a process departure (`policy.md` §1);
   ARM-1 records the corrected count. Closure: the acknowledgement.
3. **Finding 3 (major), the internal families.** All 103 cross-file pairs among the new files are
   classified (21 S, 35 G, 47 N), and round 1's 45 components each get a family class (12
   substantive, 12 small genuine, 21 incidental) and a logical family with its factoring (21
   families K1–K21). Group: ARM-2 (b), except K21 (D7, payback PR) and K18 (ARM-2 (a)).
4. **Finding 4 (major), the same-file pairs.** All 199 directed same-file hits (130 unordered
   pairs) are enumerated and classified (44 S, 15 G, 71 N) in 61 same-file components (23
   substantive, 5 small genuine, 33 incidental). Per-file totals are recomputed with them, under
   both measures; the files newly past one fifth are listed below. The screen's same-name blind
   spot inside one file is empty here (pairs log).
5. **Finding 5 (major), the host registry.** Seven draft §14 rows (H7–H13) with public contracts
   (file:line), today's consumers, resource clauses, intended generic forms and the relation to
   H1/H3/H4/H6 and the paused language-first plan: `r2/registry-rows.md`, summarized below. The
   first uses are marked the accepted exception; the gate-before-reuse rule is stated.
6. **Findings 6, 10, 11 (minors):** in **PR #93, merged 2026-10-14**. Finding 6's proposed text
   is in `r2/corrections.md`; #93's diff is bundled as `r2/pr93.diff` for the comparison.
7. **Finding 7 (minor):** the two adversarial candidates are superseded (`r2/corrections.md`).
8. **Finding 8 (minor):** the record reconciliations are drafted with exact locations
   (`r2/corrections.md`): plan rows B2 and fills-6, backlog MIG-19 and MIG-22 (**both moot**),
   design §12.8's S1b rows and §16b, the historical probes (annotate, never rewrite), the current
   probe (round 1's `AxARM` already imports `ExpTime`), and the `[Bon26]` design-context history.
9. **Finding 9 (minor):** the labels are corrected (65 policy vs 63 screened; 32 files by
   characters, 28 by code lines, 33 by either). Round 2 states both measures throughout and treats
   import-order originals as a convention. The full-path screen is being written separately; this
   round uses the flattened-copy workaround.
10. **Finding 12 (minor), helper homes:** not in #93. Two of its helpers are now ledger rows
    (`VWord.getD_drop`, M2, payback; `Path.getD_flatMap_rows`, family G-flatten, ARM-2 (a)). The
    other moves go to **ARM-2** (user, 2026-10-14; decision 7).
11. **Finding 13 (minor):** both prose corrections are drafted (`r2/corrections.md`).
12. **Finding 14 (minor):** the replay revision is stated precisely below (Attestations, item 3),
    with PR #87's file list and content hashes.

## The ledger (MEASURED screen; classification by the pack's author)

**Method.** The repository's `copy-text-screen.py`, unmodified, over byte copies named by flattened
paths (round 1's population, 210 files plus the supplement's four). `r2/scripts/pairs.py` turns
round 1's combined output into **353 unordered pairs with an added side**: 120 with library files,
103 among the added files, **130 inside one added file** (from 169, 144 and 199 directed hits).
`r2/scripts/classify.py` gives each pair a class by a rule plus named overrides:
- **library pairs**, per copy-side declaration, by inspection: **D** disclosed, **U** undisclosed
  substantive, **G** small genuine helper duplication, **N** incidental;
- **internal and same-file pairs**: **S** substantive (at least 200 shared characters of one
  specific argument or definition), **G** small genuine (a near-identical restatement: the larger
  directed share at least 90% of the smaller body, which has at least 100 characters; or the same
  statement or definition restated in another file, by named override), **N** incidental (sibling
  lemmas sharing an idiom, closure or instantiation plumbing, span artifacts). Seven pairs with at
  least 200 shared characters are overridden to N, and 19 pairs to G, each with its reason in the
  script (26 named overrides).

Each pair also gets the user's **group**: **P1** the payback PR (decided); **P1+** a row this
ledger adds to the payback list (a copy of campaign code, or riding with D4), to be acknowledged;
**A2a** ARM-2 (a); **A2b** ARM-2 (b); **X** not real duplication. A declaration counts once, with
its whole body, if it is the copy side of a counted pair (round 1's convention). Two measures, as
finding 9 asks: **whole body** (characters; code lines) and **shared text** (the largest single
overlap over its counted pairs, capped at the body; code lines prorated). Denominators: the 73
files' 421,911 body characters and 17,227 code lines.

Below-floor entries stay visible and are counted in A4+: D1 `InWin`, D5 `inWin_of_coreSum_eq`,
D6 `synOK`; **M1**, the decider banks restated per machine (10 definitions and lemmas,
`TQBFARM/Machine.decs`/`orc`/`decs_mem` against `Codec/Run.codecAs`/`orc`/`codecAs_mem`,
`PathWalkMachine.pathAs`/`pathOr`/`pathAs_mem`, and the code banks `SavitchARM/Correct.decs`/`orcN`
against `ExpBFS/Main.decs`/`orcN` and `PathHardRegs.As`/`orc`); **M2**, `VWord.getD_drop`, a Bool
specialization of the public `Programs/Util/List.getD_drop` (outside the screen population).

**Pairs by class and group** (classify log):

| Category | Pairs | Classes | Groups |
|---|---:|---|---|
| Library (added ↔ library) | 120 | D 15, U 25, G 21, N 59 | P1 18 (D 15, U 3), P1+ 15, A2a 24 (U 18, G 6), A2b 4 (U), X 59 |
| Internal (added ↔ added, cross-file) | 103 | S 21, G 35, N 47 | A2b 56, X 47 |
| Same-file (inside one added file) | 130 | S 44, G 15, N 71 | P1 1 (`decChain`/`incChain`), A2a 1 (`MReach.halt`/`trans`), A2b 57, X 71 |
| **Total** | **353** | | **P1 19, P1+ 15, A2a 25, A2b 117, X 177** |

**Totals by accounting** (ledger log):

| Accounting | Declarations | Whole body: code lines | Whole body: chars | Shared text: chars | Shared text: code lines |
|---|---:|---:|---:|---:|---:|
| A1 round 1: cross-file, every candidate (reproduced) | 151 | 3,731 (21.7%) | 108,250 (25.7%) | 42,676 (10.1%) | 1,554 (9.0%) |
| A2 A1 plus same-file, every candidate (round-1 auditor's figure, reproduced) | 242 | 5,642 (32.8%) | 163,343 (38.7%) | 73,896 (17.5%) | 2,707 (15.7%) |
| A3 cross-file, classified, N excluded | 93 | 2,416 (14.0%) | 72,338 (17.1%) | 37,089 (8.8%) | 1,310 (7.6%) |
| A4 A3 plus same-file, classified, N excluded | 149 | 3,972 (23.1%) | 117,468 (27.8%) | 64,109 (15.2%) | 2,280 (13.2%) |
| **A4+ A4 plus the manual entries: the ledger for acknowledgement** | **163** | **4,009 (23.3%)** | **118,313 (28.0%)** | **64,482 (15.3%)** | **2,297 (13.3%)** |

**A4+ by class and by group** (each declaration once):

| Class | Decls | Code lines | Body chars | Shared chars |
|---|---:|---:|---:|---:|
| D disclosed | 18 | 304 | 7,799 (1.8%) | 6,956 |
| U undisclosed substantive (library) | 12 | 513 | 13,990 (3.3%) | 7,146 |
| G small genuine (library) | 17 | 140 | 3,403 (0.8%) | 1,615 |
| S internal substantive | 20 | 1,197 | 40,521 (9.6%) | 18,810 |
| S same-file substantive | 42 | 1,440 | 43,111 (10.2%) | 24,207 |
| G internal small genuine | 29 | 273 | 6,831 (1.6%) | 3,650 |
| G same-file small genuine | 14 | 116 | 2,019 (0.5%) | 1,812 |
| M1 / M2 manual | 10 / 1 | 24 / 2 | 605 / 34 | 259 / 27 |

| Group | Decls | Code lines | Body chars | Shared chars | Owner; window; gate |
|---|---:|---:|---:|---:|---|
| **P1** payback PR, decided | 20 | 336 (1.9%) | 8,641 (2.0%) | 7,641 (1.8%) | maintainer; after the B6 hosts (#92, merged 2026-10-14); its own full gate |
| **P1+** proposed payback rows | 14 | 98 (0.6%) | 2,269 (0.5%) | 1,291 (0.3%) | the same, if acknowledged |
| **A2a** ARM-2 (a) | 10 | 259 (1.5%) | 7,256 (1.7%) | 2,254 (0.5%) | the user's refactor, coordinated with Hydroxyi before any brief; not scheduled; a PR plus its gate (zone rules) |
| **A2b** ARM-2 (b) | 119 | 3,316 (19.2%) | 100,147 (23.7%) | 53,296 (12.6%) | the same |
| **X** not real duplication | — | — | — | — | 177 pairs, no action; 18 library copy-side declarations are N only |

Whole-body figures are conservative: a long proof counts entirely when it reproduces half of a
short declaration, and a declaration in two groups counts under the first. The net view (one member
of each internal or same-file component, earliest in import order, treated as the original) gives
125 declarations and 87,530 body characters (20.7%): an accounting convention only.

**Files past one fifth** (A4+; MEASURED; the measures as finding 9 asks):
- **whole body, characters: 34 files** (round 1: 32); **whole body, code lines: 29** (round 1:
  28);
- **shared text, characters: 20 files** (round 1: 14): `Codec/Langs` 61.0%, `TQBFARM/Semantics`
  56.7%, `Machines/ARMLoops` 56.5%, `Machines/VWord` 53.4%, `Codec/Layout` 45.2%, `Codec/Layout2`
  43.7%, `SavitchARM/Run` 41.3%, `Codec/Engine` 40.2%, `Machines/NARMProof` 38.3%, `Codec/Bridge`
  37.9%, `ExpBFS/Relax` 37.6%, `Machines/NARMCompile` 33.3%, `Logspace/PathWalkProof` 29.9%,
  `TQBFHardTseitin` 28.0%, `Machines/ARMWidth` 27.7%, `ExpBFS/Run` 23.9%,
  `Logspace/ISCountGenWalk` 22.6%, `Machines/MARMCompile` 22.0%, `Codec/Deciders` 21.6%,
  `Machines/MARM` 21.4%;
- **shared text, code lines: 18 files** (round 1: 13).

**Newly past one fifth** (A4 against round 1's ledger A1):

| Measure | Newly past | No longer past (only incidental pairs had taken them over) |
|---|---|---|
| whole body, characters | `TQBFHardSemantics`, `Codec/Deciders`, `Codec/Langs`, `Codec/Parse`, `ExpBFS/Run`, `Logspace/PathHardRegs`, `Logspace/PathWalkProof`, `Machines/ARMLoops` | `TQBFHardVerifier`, `Codec/Scan`, `Codec/Word`, `Logspace/ISCountGenCorrect`, `Logspace/ISCountGenRadius`, `Machines/NARMKit` |
| whole body, code lines | the eight above and `Machines/ARMWidthExample` | `TQBFARM/Machine`, `TQBFHardVerifier`, `Codec/Scan`, `Codec/Valid`, `Codec/Word`, `Logspace/ISCountGenCorrect`, `Logspace/ISCountGenRadius`, `Machines/ARMReach` |
| shared text, characters | `Codec/Deciders`, `Codec/Langs`, `ExpBFS/Run`, `Logspace/ISCountGenWalk`, `Logspace/PathWalkProof`, `Machines/ARMLoops`, `SavitchARM/Run` | `TQBFARM/Machine` |
| shared text, code lines | the seven above | `TQBFARM/Machine`, `Machines/MARMCompile` |

Every newly past file is past by its same-file pairs (each is also in the "newly past against A3"
list of the ledger log). ARM-1 and ARM-2 are the `workflow.md` §4 human-review items; the scope
below extends ARM-1's.

**The twelve undisclosed substantive copies** (finding 2; MEASURED shared characters; contracts and
groups the pack author's):

| Copy (file:lines) | Source (file:lines) | Shared | Shared contract that removes it | Group |
|---|---|---:|---|---|
| `Machines/ARMWidth.lean:104-179` `arm_decides_space` | `Machines/ARMProof.lean:223-333` `arm_decides` | 1,681 | one decision-bridge core over a step-semantics interface (bank setup, the `PreS`→`Pre` case split, `cleanRun_mono`, the cell arithmetic) | A2b |
| `Machines/MARMTime.lean:444-556` `marm_dtime` | `arm_decides` | 1,652 | the same core, with the time conclusion from `runFrom_count_eq` | A2b |
| `Machines/NARMProof.lean:195-239` `narm_decides` | `arm_decides` | 646 | the ND bridge as an instance of the core, through `detPart` | A2a |
| `Machines/NARMProof.lean:85-122` `npre_of_npreS` | `arm_decides` | 642 | a public "syntactic precondition gives the bank precondition" lemma | A2b |
| `Machines/NARMProof.lean:139-182` `narm_decides_space` | `arm_decides` | 583 | the core | A2b |
| `Codec/Engine.lean:83-101` `decChain` | `Logspace/InputAccess.lean:621-646` `arm_increments` (private) | 423 | one public parameterized chain lemma and stride decoder in `InputAccess` (with D7) | **P1** |
| `Machines/MARMTime.lean:214-332` `runFrom_count_eq` | `ConfigCount.lean:313-340` `coreCode_inj` | 314 | the windowed tape-code injectivity sub-argument as a lemma | A2a |
| `Machines/NARMProof.lean:247-265` `narm_decides_poly` | `Machines/ARMKit.lean:78-93` `arm_decides_poly` | 270 | one width-reduction lemma | A2a |
| `Machines/NARMCompile.lean:139-163` `spaceUsedWith_le_of_ranges` | `Machines/Compile.lean:226-242` `spaceUsed_le_of_ranges` | 240 | one ranges lemma over visited positions, `runFrom` and `runWith` instances | A2a |
| `Machines/MARM.lean:191-200` `MReach.halt` | `Machines/ARMProof.lean:80-88` `AReach.halt` | 233 | reachability once over an arbitrary step relation | A2a |
| `ClassPSPACE/TQBFHardParams.lean:175-187` `length_lbStep` | `ClassNP/PolyTimeBlockLoop.lean:676-691` `length_xorPairStep_le` (private) | 207 | one shared pair-step length helper | **P1** |
| `Machines/MARM.lean:180-188` `MReach.trans` | `Machines/ARMProof.lean:68-76` `AReach.trans` (also `Parse2`, `ParseCmp`, `DblLang`) | 200 | the same reachability kit | A2a |

(Paths under `TCSlib/Complexity/SpaceComplexity/` unless they start with `ClassPSPACE/` or
`ClassNP/`. What each shares, in words: `r2/ledger-r2-tables.md` §2.)

**The 35 small library overlaps** (per copy-side declaration; `r2/ledger-r2-tables.md` §1, §3):
- **17 small genuine** (G), each with a proposed shared helper:
  - copies of campaign code, **proposed for the payback PR (P1+)**: `orc_bit`/`orc_len` in
    `TQBFARM/Machine` and `Codec/Run` (QueryReshape's private `drop_bit`); `canon_of_getLastD`,
    `getLastD_of_canon` (QueryReshape's private `drop_canon`); `pe_getD_snd` (Mult's private
    `mult_addresses`); `outSummary_eq_empty_iff` (beside ConfigGraph's `outSummary_eq_accept_iff`);
    `prefixTruth_congr_agree` (`QBF.prefixTruth_congr`); `pt_rep_mul` (CookLevin's private
    `clA5Times_native`); `vword_whole₂`/`₃` (`InputAccess.vword_whole₁`, with D7); and
    `toCNF_extension_iff`, which re-proves DAGCircuitSat's private `eval_tseitinGates_values`
    (with D4);
  - copies of Hydroxyi's earlier library (A2a): `MHalt.mono` (`AHalt.mono`),
    `eq_bits_append_replicate` (`Parse.canon_eq_bits`), `foldr_max_le` (a fourth copy beside
    `TreeDAG`, `DAGTransform`, `DAGFanin`), `getD_flatten_block`
    (`PSubsetPPolyConfigCircuit.getD_flatMap_chunk`, with `Path.getD_flatMap_rows`);
- **18 incidental** (N, not real duplication): `lbStep_iterate`, `polyTimeComputable_levelBits`,
  `prefixTruth_imp_const`, `prefixTruth_and_const`, `pt_take`, `pt_drop`, `pt_vwid`, `pt_orB`,
  `halvCount_loop`, `slide_ok_iff`, `cellOf_congr`, `mrunFrom_eq`, `mcompileTM_init`, `marm_run`,
  `last_tape_run`, `ndtm_runWith_eq_runFrom`, `arm_reach`, `rawEdge_adjWordE` (induction and
  `simp` preludes, lockstep-run idioms, closure plumbing).

**The internal and same-file families** (`r2/ledger-r2-tables.md` §4–§5; all A2b unless marked):

| Family | Pairs (class: count) | Representative | Factoring |
|---|---|---|---|
| K1 register kit | internal G 13, S 3 | `cpI`, `shI` 100%; `Bd.toV` with the scoped `regs` macro, 497 | one block kit and one register-record tactic |
| K2 decider banks, oracle lemmas | internal G 18 (+ M1) | `orc_bit` 100% | public input and code banks with their oracle lemmas |
| K3 bridge plumbing | internal S 4 | `arm_decides_space`/`marm_dtime`, 1,122 | ARM-2's single bridge over one step-semantics interface |
| K4 `detPart` compile bridge | internal S 4, G 1; same S 2 | `mdet_halt`/`ndet_halt`, 595 | one "compile with overridden states" bridge |
| K5 one-step `NHalts` | internal S 2; same S 1 | `NHalts.choose`/`NTerm.nhalts`, 282 | one one-step lemma |
| K6 code languages, deciders | internal S 1, G 1; same S 4, G 7 | `stepLang_mem`/`one_run`, 1,308 | one parameterized code language, one decider lemma |
| K7 layout runs | internal S 1 | `layout_run`/`layout2_run`, 4,139 | one layout run |
| K8 parse phases | same S 1 | `parse_run`/`parse_run₂`, 1,615 | common phases once |
| K9 missing citations | internal S 2 | `validChk_iff`/`word_split`, 341 | cite |
| K10 MARM loops and steps | internal S 4; same S 6, G 6 | `inner_run`/`outer_run`, 1,804 | counted MARM loop, clear block, one step lemma |
| K11 ARM transfer loops | same S 12 | `dmove_run`/`move2_run`, 774 | one transfer loop; `ARMWidthExample` cites `ARMLoops` |
| K12 IS guess loops | same S 2 | `guloop`/`gvloop`, 1,274 | generic guess loop |
| K13 PATH endpoint phases | same S 2 | `ps_scmp`/`ps_tcmp`, 1,953 | one endpoint-field comparison |
| K14 Savitch tails, push/pop | same S 8 | `pushU_run`/`pushV_run`, 724 | one tail and one push lemma |
| K15 register-record ext. | same S 1 | `eq_qk`/`eq_yid`, 687 | one extensionality lemma |
| K16 TQBF walk block | same S 1 | `node_run`/`qlook_run`, 297 | one labelled block |
| K17 TQBF hardness | same S 2, G 1 | `prefixTruth_replicate_all`/`_ex`, 422 | bound lemma; block lemma over the quantifier |
| K18 reachability kit (A2a) | same G 1 | `MReach.halt`/`trans`, 197 | with U-reach |
| K19 padding key | same S 1 | `NGood.mono`/`seg`, 214 | one padding lemma |
| K20 citations | internal G 2 | `two_pow_bits_le`/`bitsVal_le_of_width`, 196 | cite one |
| K21 chains (**P1**, D7) | same S 1 | `decChain`/`incChain`, 478 | the decided stride decoder |

`ARMWidthExample.d1_loop`/`d2_loop` re-prove `ARMLoops.dmove_run`/`move_run`; `ARMLoops` is not
in that file's import closure (MEASURED, import graph).

### Acknowledgement (the user's; left blank by the builder)

> **Acknowledged by the user on 2026-10-14. Scope: the complete classified ledger of
> `r2/ledger-r2-tables.md`** (A4+: 163 declarations, 15.3% of the received code by shared text;
> 19 P1, 15 P1+, 25 A2a and 117 A2b pairs; 177 pairs classified not real duplication), **with the
> payback PR's decided list, the 15 proposed P1+ pairs (13 declarations) and the manual row M2
> added to it, and ARM-2 for the rest, including finding 12's other helper moves; owners and
> windows as tabled.**
>
> *Given by the user in the maintainer's session on 2026-10-14 (decisions 5–7 above) and entered
> here by the maintainer. The acknowledgement is of scope; whether the scope is complete is the
> auditor's ruling (brief, point 1).*

## The host registry draft (finding 5)

Full rows with contracts, consumers, resource clauses, generic forms and relations:
`r2/registry-rows.md`. Summary in the registry's columns:

| # | Host | Status | Named consumers |
|---|---|---|---|
| H7 | ARM compiler (`compile_correct_from`) and decision bridges (`arm_space`, `arm_decides*`, `arm_decides_space`/`_SPACE`/`_pspace*`); loop and reach kit | received 2026-10-14; public, ungated; **accepted exception**; no time clause | H13a, H13e, H10's deciders, H13d's bits; through H8/H9 the ND and time customers |
| H8 | NARM: `ncompileFinNDTM`, `narm_space`, `narm_decides*`, `NSem.decides` | the same | H13b, H13c |
| H9 | MARM and its time bridge: `runFrom_count_eq`, `marm_dtime` | the same | H12 |
| H10 | Configuration codec and code deciders: `cfgCode`, `cfgCode_lt`, the four languages in `LOGSPACE`, `mem_iff_codeChain` | the same; `InWin` retires (D1) | H13a, H13b, H13d, H12, H13f |
| H11 | Indexed input access (ours): `inputBitLang`/`inputLenLang`, `boundedDecode_loop`, `PreimageHost` | existing; now a host with received consumers; D7 decided | every received customer |
| H12 | Code reachability, growing window (`ExpBFS`): `rset`, the stop rule, `NSPACE_subset_exp_dtime_of_le` | received; **accepted exception**; MIG-19 moot | `ExpTime` (3 theorems), H13b |
| H13 | Customer machines: (a) Savitch, (b) inductive counting, (c) PATH walk, (d) PATH hardness, (e) TQBF walk, (f) TQBF hardness | received; **accepted exception** | `PSPACE_eq_NPSPACE`; `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; `PATH_mem_NL`; `PATH_NLComplete`; `TQBF_mem_PSPACE`; `TQBF_PSPACEHard`, `_Complete` |

**Gate before reuse.** No further consumer of H7–H13 is briefed until that row's public contract
has passed a contract gate (of the contract as listed or of its generic form). The generic forms
are ARM-2's direction, designed with Hydroxyi. The draft also gives reconciled text for H1 (the
machine form exists; the `b4m*` core goes with D6; MIG-22 moot), H3 (consumers), H4 (built at ARM
level for `NSPACE ⊆ DTIME(2^O(S))`; MIG-19 moot), H6 (TQBF hardness served by H13f) and the
pure-kit paragraph (four new reachability notions).

## The minor fixes and records

- **PR #93 (merged 2026-10-14; replay 74 of 74):** findings 6, 10, 11. Its diff is bundled as
  `r2/pr93.diff` (`git diff e831b5b0 3fe6a2de`, the PR's head); the round-2 auditor checks it
  against `r2/corrections.md`.
- **Not in #93:** finding 12's helper moves (ARM-2, decision 7); findings 7, 8, 9, 13, 14 are pack
  and record texts (`r2/corrections.md`), landed by a records commit.

## Brief for the auditor

Points to rule on:

1. **The classified ledger is complete and correctly classified** (findings 1–4). Check that:
   - `r2/pairs.tsv` enumerates every pair of round 1's combined screen output with an added side
     (512 directed hits, 353 unordered), same-file pairs included; rerun `pairs.py`;
   - the classification rule and the 26 named overrides (`classify.py`) are sound. Challenge in
     particular: the seven overrides to N with at least 200 shared characters (`S017`, `S047`,
     `I020`, `I080`, `I072`–`I074`); the G overrides of restated lemmas with lower text share
     (`I009`–`I013`, `I042`, `I043`, `I056`, `I057`, `I071`, `I082`–`I085`, `I016`, `I017`,
     `I023`, `I081`, `I064`); and the 18 library declarations classified incidental;
   - the twelve U rows: sources, shares, the stated contracts;
   - the per-family factorings are real (one parameterized declaration, or a citation, removes the
     repeat);
   - the manual entries (D1, D5, D6 below the floor; M1; M2), and whether other semantic
     duplicates escape the text screen (the pack found `d1_loop`/`d2_loop` by inspection; it does
     not claim a complete semantic search).
   Then rule whether the scope proposed for acknowledgement is the **complete** scope.
2. **Groups.** Is each row in the right group under the user's decisions: (1) the payback PR's
   decided list, the P1+ rows (copies of campaign code, or riding with D4), ARM-2 (a) and (b), or
   not real? Are the P1+ proposals proper payback rows (each removes a copy of campaign code, or of
   D4's file, by a promotion, a move or a citation), and is any decided row missing a consumer check (D6's 45 private
   declarations have no reference outside their range; records log)?
3. **The measures** (finding 9). Recheck A1 and A2 against round 1, and A3–A4+ from the inputs.
   Do the "files past one fifth" lists follow from the per-file table, under both measures and both
   units? Is reporting A4+ (N excluded) rather than A2 (every candidate) the right basis for the
   acknowledgement, given that A2 is also reported?
4. **The registry rows** (finding 5). Are the contracts, consumers and resource clauses right
   (check against the bundled sources), and do the rows, the accepted-exception status and the
   gate-before-reuse rule meet *hosts come first* and decision 3? Are the H1/H3/H4/H6
   reconciliations accurate?
5. **The corrections** (findings 6–14): is each proposed text exact? Finding 6's sentence against
   the proof; finding 7's candidates; the finding-8 records (including the D6 count: 45 declarations
   where ARM-1 says 44); the finding-13 sentences; the finding-14 statement against the C1 delta
   log.
6. **Adversarial checks** (at least six), for example:
   - a pair overridden to N whose shared text is really one argument;
   - a G restatement whose statements differ in a hypothesis (so citing the shared lemma would not
     typecheck);
   - a family whose proposed factoring would change a public statement (then it needs a statement
     gate, not a swap);
   - an added file whose one-fifth status flips under the other measure or unit;
   - a library counterpart whose tip line differs from the received line (the drift log lists the
     two);
   - a registry consumer that is not an importer, or an importer missing from a row;
   - a P1+ row whose original is private in a colleague's file (the payback PR then needs his
     clearance, as D4 does).
7. Report anything else this pack, `r2/registry-rows.md`, `r2/corrections.md` or
   `r2/ledger-r2-tables.md` misstates.

## Repository-side attestations (verify or challenge)

MEASURED = computed by a round-2 script, log attached. ESTIMATE = a judgement or a text-level
check. One runner pass (`r2/scripts/run_r2.zsh`, exit 0).

1. **Environment** (MEASURED). No Lean, no `lake`, no olean written. Python as `python3 -I`. Git
   read-only (`rev-parse`, `cat-file`, `diff`, `log`, `show`, `grep`, `merge-base`). Every full hash
   came from `git rev-parse`, and every hash-like token of this pack, `NOTES.md`,
   `r2/corrections.md` and `r2/registry-rows.md` resolves to a git object it prefixes (hashcheck
   log). Everything was written under the builder's folder.
2. **Identity** (MEASURED, provenance log): the 81 received `.lean` files are byte-identical at
   `8c23f3bc`, `733c22b7` and the tip; the Lean trees of `39bfdca4` and the tip are identical; the
   73 copies' SHA-256 equal round 1's labels.
3. **The replay revision** (finding 14). Round 1's maintainer execution claims (its replay and
   axiom logs, not re-run here): the replay (147 modules, 0 failures) and the axiom probe (60
   prints, all within the standard three) ran at `733c22b7`, C1's branch (`21216a49`) merged with
   `dc891632`, from an existing olean snapshot. MEASURED here (C1-delta log): that tree is the received tree plus exactly PR #87's diff: `d054888d..4d149798` and
   `dc891632..733c22b7` are byte-identical (SHA-256
   `7d9dfcf2ac891da013cd182c80c4cdf14853111a8337cb4b2a08171bd468d3bd`), 10 Lean files:
   `ClassNP.lean`, `ClassNP/ExhaustiveReplay.lean` (new), `Diagonalization/NTimeHierarchy.lean`,
   `TuringMachine.lean`, `TuringMachine/Build/InputWindow.lean` (new), `Build/NDHost.lean` (new),
   `TuringMachine/ChoiceReplay.lean` (new), `TuringMachine/NDCodeSimulator.lean` (new),
   `TuringMachine/Nondeterministic.lean`, `TuringMachine/NondeterministicSpace.lean`; blob ids and
   SHA-256 in `r2/corrections.md` and the log. Two are upstream of the received modules
   (`Nondeterministic`, `NondeterministicSpace`), where C1 proved the two lemmas that are `sorry`
   at the received tree (`runWith_eq_fixChoice_runFrom`, `spaceUsedWith_eq_fixChoice_spaceUsed`).
   At the received tree no code outside their own headers names either lemma (ESTIMATE: a
   comment-stripped text scan). The logs therefore certify the received code on top of C1; no probe
   of the exact received tree was run.
4. **Screen and ledger reproduction** (MEASURED): the added-only screen reproduces byte for byte;
   round 1's ledger reproduces byte for byte; A1 and A2 equal round 1's and the round-1 auditor's
   figures (151 / 3,731 / 108,250 / 42,676; 242 / 5,642 / 163,343 / 73,896; 28 files past one
   fifth on A2's shared text).
5. **Pairs and classes** (MEASURED counts; classification ESTIMATE, the pack author's): 353 pairs;
   classes and groups as tabled; every S or G internal or same-file pair has a logical family
   (families log).
6. **Records behind the decisions** (MEASURED, records log): `InWin` 48 code uses in 7 files;
   `inWindow_iff_cfgInWindow` used only in `ConfigGraph`; `TQBF.lean` 2474–3185 holds 45 private
   `b4m*` declarations with no reference outside the range or the file; no code reference to
   `s1b_*` outside `ConfigGraph` (the one hit, `ShapeFixtures.s1b_binderkinds`, is an unrelated
   name).
7. **Registry inputs** (MEASURED, registry log): declaration lines (comment-stripped headers) and
   the direct importers of each component at the tip.
8. **Drift** (MEASURED, drift log): as above; no non-incidental pair touches a library file that
   changed since the received tree. #89 and #91 change comments only (comment-only log). Round 1's
   combined screen output, which `pairs.py` reads (`r2/inputs/screen-combined.out`), is the
   full-population output verbatim followed by the supplement's 215 pairs that involve its four
   extra files (provenance log).
9. **Not established here:** any Lean elaboration; the contents of PRs #92 and #93; a semantic (not
   textual) duplication search; the classification itself beyond the stated rule and inspection.

## Bundle

`r2/BUNDLE-FILES.txt` lists every path, in order: this pack, round 1's findings and pack, the
standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`), the response, the backlog at the tip
(ARM-1 and ARM-2), the design document and the plan (whole; round 1's §14 extract too), the round-2
evidence, inputs, scripts and logs, round 1's ledger log, labels, disclosure table and scripts that
round 2 reads, round 1's axiom probe, the 73 added files, and the 27 library files the ledger rows
and the registry cite: 169 files, about 5.2 MB, plus the maintainer's `r2/pr93.diff` (170). Not
included: round 1's screen logs (the combined input stands for them), the library files that only
incidental pairs touch, and #92's diff (see the maintainer note).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (debt: failure mode 5). Findings go verbatim into
`audits/arm-extensions-fill-r2-findings.md`. The gate closes when this round reports zero blockers
and zero majors, with the user's acknowledgement recorded for the duplication majors.
