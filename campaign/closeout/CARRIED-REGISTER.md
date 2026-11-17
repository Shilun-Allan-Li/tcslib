# Carried-debt register at the chapters 3–4 closeout (final at stage 3, 2026-11-17)

This is stage 3's record (`STAGES.md`). It lists every measured family the closeout leaves in
place, why, and the first step if it is taken up later. Figures come from
`R3-R6-MEASUREMENT.md` and the stage notes.

- **Rule-10 exposure** is the number of member / use proofs that would fail the sealed check if
  touched, so they would need repair.
- **Seyoon's rulings** are dated; the rest follow the measurement note's recommendation, which
  Seyoon adopted with the stage plan (2026-11-16).

## Large families (not worth a closeout PR)

| Family | Where | Size | Exposure (m/u) | Why carried | First step if taken up |
|---|---|---|---|---|---|
| **R5: the ARM-layer K-families** (K1–K5, K7–K16, K18–K20, MT-1, AS-2, ARM-1 residue) | SpaceComplexity ARM programs, the reachability kit, input/code banks | K18: 28 members, 161 lines, 140 uses; MT-1: 553 lines; AS-2: 685 lines | 310 in total (K18 alone 27 / 116) | About 9× R3's repair load; the debt is design-group D4's (the ARM layer) | Per-kit design notes, starting with K18 |
| **U-1 / MIG-2**, the universal host interface | `Universal` (`timedCut*` layer) | 72 members, 1,411 lines, 22 uses | 44 / 0 | The largest single item; needs a host-interface design | A design note |
| **MIG-24**, symmetry lemmas | across the machine library (with ZoneRebalance) | 37 members, 546 lines, 186 uses | 28 / 80, plus ZoneRebalance (unmeasurable: its metadata step runs out of memory) | High use count | Per-directory slices |
| **MIG-9**, the bit-length counter row | ClassP and Build counters | 34 members, 615 lines, 20 uses | 21 / 14 | Needs a new counter row | A design note |
| **F7-1(b)** | Build/CertShell and its users | 9 members, 229 lines, 23 uses | 9 / 15 | Assigned to MIG-14 | With MIG-14 |
| **DT-1**, `mem_DTIME_iff` readers | ClassP consumers | 2 members, 5 lines, 26 uses | 0 / 23 | A 23-reader repair under a replay of most of the tree, for 5 lines | When `DTIME`'s readers are next opened |
| **The MIG migration rows outside the closeout** (MIG-11 to MIG-23, including **MIG-16**, Build/OracleSim) | Build contract layer | per backlog table (MIG-16: −250 to −400) | not measured | Depend on MIG-0; outside chapters 3–4 | Kept in the register (Seyoon, 2026-11-16) |

## Small items carried by ruling

| Item | Ruling | Reason |
|---|---|---|
| **SG1 kind 6**, the SAT/Hardness host dispatcher, with kind 3's remaining private twins (`satPadTM`, `satPad_run`, `satPad_words`, `satHost_seam`/`_call`) | Seyoon, 2026-11-16 | A public host needs an envelope design |
| **R4 item 13** (`clPlacement`) | Seyoon, 2026-11-16 | A private layout adapter, not copy debt |
| **SH-1**, Nondeterminism's certificate shell | Seyoon, 2026-11-16 | Needs a halting native-input choice core; about +25 to +85 lines to retire one 4-line pair (backlog §SH-1) |
| **MIG-8's merge half** | follows SH-1 | Waits on SH-1 |
| **RS-1**, the restart identity's three remaining sites | Seyoon, 2026-11-16 | The sites compare against constructed configurations; a citation saves almost nothing |
| **C1E-1(d)'s optional merge** of ExhaustiveReplay's nine one-bank update lemmas | Seyoon, 2026-11-16 | Needs a bank-indexed layout redesign |
| **F6-1(f)**, `oracleEmbed_updateTape` | Seyoon, 2026-11-16 | No second copy exists; goes with MIG-16 |
| **CC7-1's per-record bound's base half** | — | Done in stage 1 (one private `skipAction_consumes`); listed here for completeness |
| **MIG-6** (`Codes2Tape` by tape count) | Seyoon, 2026-11-16 | Redefines frozen two-tape code structures |
| **R2c**, the §12 sibling rows (12.2c item 5) | Seyoon, 2026-11-16 | Measured with the R2c scanner (`R2C-SCANNER.md`): retiring them would grow the files by 361 lines (to 4,643) and add 10 net screen pairs (19 new, 9 gone) |
| **CK-1**, the codec deciders' check readers | Seyoon, 2026-11-17 | Gate 153's seal: touching `acceptLang_mem`/`initLang_mem` exposes older reads of Codec/Machine's `CA` table and `CMode` instance; a repair needs two new `CA_vDone_*` table lemmas. The two `_def` lemmas were dropped with it |
| **IR-1's ExhaustiveReplay copy** (`xr_inRewindTM`) | Seyoon, 2026-11-17 | The public `inputRewindTM_run` needs the input head at position 1 or more, but the replay rewinds from position 0 too. Covering it needs a new zero-start lemma in Build/InputRewind, which grows the net count. The ER machine already runs on the generic `FinTM.timed_rewind`. UniversalK's copy is retired (stage 2, Fill A) |
| **RN-1's `universalCapture_embed`** (UniversalStartup, new in #350) | Gate 154 G154-02 (2026-11-17) | Citing `Cfg.mapState_eq_of_fields` needs a CfgFacts import into chapter 1's UniversalStartup (not approved); about −2 lines |
| **G147-01**, two stale historical notes in Nondeterminism | Seyoon, 2026-11-17 | Gate 153's seal: editing the docstrings of `ntime_expPow_subset_NEXP` and `EXP_eq_NEXP_of_P_eq_NP` exposes their direct `NTIME`/`NEXP` reads, and `NEXP` has no published reader. The notes still name two deleted lemmas; the W5/W6 docs pass may revisit them |

## Carried by the refactor plan's register (REFACTOR-PLAN.md §3–§4; added after gate 158, G158-05)

| Item | Ruling | Where | Reason | Pointer |
|---|---|---|---|---|
| **CH34-D3**: `exists_uniformMachineCode2` against EXPCOM's structure | Seyoon, 2026-11-16 ("Agreed") | `Diagonalization/EXPCOM`, its uniform machine code | Acknowledged as forced (B261). Unifying would redefine two frozen, audited structures (a statement change and its own gate) to save about 12 lines | REFACTOR-PLAN §3.1 |
| **RW-1**: the rewind row's copies of Catalog's seek frame and skip-back table | user, 2026-10-18 (acknowledged); kept in the register at the closeout | `Build/Rewind` against `Build/Catalog` (`rw_cfg` against `catalogSeekCfg`; `rewindTM` against `skipBackTM` and the seek tables) | A record update over a different phase type and one shared 140-character table block; no proof copied. Retirement waits for Catalog's next edit | `duplication-ledger.md` RW-1 |
| **`zfBFallback`**, CH34-D2's approved residual | user, 2026-10-11 (PR #19, gate closed 0/0/0) | `Codes2Tape` | The one adaptation left (23 → 1) after the format-parameterized parse layer; approved as a residual | ledger, CH34-D2 row |

**Optional scope, not counted debt** (REFACTOR-PLAN §3.2; Seyoon, 2026-11-16: "leave out of the
closeout, listed in the register as optional"):
- the original Loop host's 110 pairs (P item 11);
- the ch7 embedding-layer watch (MIG-5);
- BL-W, WC-1, QF-1 and RC-1 to RC-3;
- P item 12's clocks;
- the SafeSegment sibling.

## Blueprint follow-up outside the chapter scope

- **712 stale chapters 1–2 entries** (gate 157, G157-03; Seyoon, 2026-11-17: delete in a later
  small PR). They were deleted by PR #362 (merged `07c94b48`, 2026-11-17, without an audit by
  Seyoon's ruling). Nothing remains carried here.

## Standards-lint items in the chapter scope (carried by ruling, Seyoon 2026-11-17)

Found by W6's lint (`campaign/gates/158-w6-final/evidence/lint/`). They are long-standing and
disclosed to the final audit, not fixed.

| Item | Where | Note |
|---|---|---|
| **Files over the 1,000-line limit** (policy §1) | NTimeDiagonalizer 8,466; Hierarchy 3,439; Inclusions 2,861; Ladner 2,739; QueryReshape 2,625; InputAccess 2,159; NTimeHierarchy 1,934; TQBF 1,866; Padding 1,769; WindowClock 1,677; Mult 1,474 | A split moves thousands of lines into new modules and needs a full replay. The first step, if taken up, is per-file split plans starting with NTimeDiagonalizer |
| **Module docstrings without `## Main definitions`** | 13 modules (list in the lint output) | Documentation only |
| **Umbrella import files without the standard `set_option` lines** | `ClassOracle`, `ClassPSPACE`, `Diagonalization`, `SpaceComplexity`, `TimeHierarchy` | Import-only files |

**All 69 flags, classified after gate 158 (G158-06;** `evidence/lint/LINT-CLASSIFIED.json`**):**
- **39 carried by the ruling above:** 15 option-line flags (the 5 umbrella files, three lines
  each), 13 missing `## Main definitions` sections, 11 oversized files.
- **8 false positives:** module prose that the lint parses as a declaration (for example
  `NTimeHierarchy.lean:32`, "theorem at book strength").
- **16 proof-sketch flags inflated by the signature.** The lint counts the signature as proof;
  each body is at most 20 lines.
- **6 genuine items, not covered by the ruling above; disposition pending Seyoon:**
  - proofs over 20 lines without a proof sketch: `mult_contribution` (28), `mult_next_column`
    (23), `mult_validate_field` (25) in `Logspace/Mult`; `compQ_length_le` (21) in
    `Logspace/QueryReshape`; `searchDown_run` (21) in `Machines/NARMPSem`;
  - `Machines/Parse.lean`'s module docstring has no `## Main results` section.

## Overlap with `cryptography/pass-shelat-ch2-4`

`CH2-4-OVERLAP.md` gives the details. The first row is prospective: it arises when ch2-4 merges
into `main` after this campaign. The second row is already in the tree, adopted in #354 (corrected
after gate 158 round 2, G158-R2-01). Home and ownership are for both campaigns to decide.

| Item | Source | Note |
|---|---|---|
| **The clean-module layer, twice** | ch2-4's `Build/ModuleHost` (gate 03l) against this campaign's `ClassNP/CleanCall` and SAT's private host (R4-1, R4-2) | Both harvested SAT's private module layer to different homes. ModuleHost has Randomized and Cryptography users; CleanCall has SAT. One can cite the other later |
| **Duplicate readers (already in the tree)** | `encodeNat_def`/`encodeNat_eq`; `indicator_def` beside `indicator_of_mem`/`_not_mem` | Adopted in #354 so that ch2-4's merge is clean. Unlike the clean-module layer above, these exist in the tree now; they are small duplicate facts |

## Done in the closeout (for contrast)

The waves R0–R4 and the R3/R6 items: gates 142–152 (#328–#345), stage 1 (#349, gate 153; CK-1 and G147-01 carried) and
stage 2 (fills A–C; #350, gate 154), the ch2-4 compatibility PR (#354, gate 155) and the `main`
sync (W4; #356, gate 156). Per-family entries are in `duplication-ledger.md`.
