# External audit pack — the ARM extensions (received code), round 3: the payback re-measured, `arm_reach` open

Round 3 of the fill-style gate of Hydroxyi's merge `8c23f3bc`. Round 2
(`audits/arm-extensions-fill-r2-findings.md`, attached verbatim; resolutions
`audits/arm-extensions-fill-r2-resolutions.md`): **OPEN, 0 blockers, 2 majors, 6 minors** (bundle
SHA-256 `59c8f436cdbf16f1a155d4f9d0c648e8bbd43e8292f4168d7c5e3e23c494b490`, 170 sections,
dispatch folder 21). The round-1 and round-2 packs and bundles are immutable; this pack
supplements them. The gate closes on a round with **zero blockers and zero majors**; a duplication
major closes only by the user's explicit acknowledgement, recorded with its named payback. Record
findings in `audits/arm-extensions-fill-r3-findings.md`.

Since round 2, the dedup payback (round 2's "Next", item 1, and the payback PR of ARM-1) was built
and **landed as PR #101**. This round re-measures the ledger on the payback tree, presents the
payback as the refactor's diff, and reports every round-2 finding's status. One copy is **not**
removed: `arm_reach` (pair L066) waits for Hydroxyi. The auditor is asked whether the gate can close
with it recorded as acknowledged debt (next section).

Conventions. `r3/` is `audits/evidence/arm-fill/r3/`, `r2/` is `audits/evidence/arm-fill/r2/`,
`payback/` is `r3/payback/` (the landing material of #101), and "the X log" is
`audits/logs/arm-fill-r3-X.log`. Source paths beginning `Machines/`, `Codec/`, `Logspace/`,
`ExpBFS/` or `SavitchARM/` are relative to `TCSlib/Complexity/SpaceComplexity/`; `ClassPSPACE/`,
`ClassNP/`, `CircuitComplexity/`, `Formulas/` and `CookLevin/` to `TCSlib/Complexity/`. Pair ids are
round 2's (`r2/pairs.tsv`); pairs new in round 3 are `L3-*` (new at the landed tree) and `T3-*` (new
at the tip). Classes and groups keep round 2's meanings; **A2w** is new: ARM-2 and the user's dedup
window, with a home decision (G-rep). Accountings: **C** every candidate (round 2's A2), **K**
classified with N excluded (A4), **K+** K plus the manual rows (A4+, the acknowledged basis).

## The question for the auditor: `arm_reach` (L066), open debt

**The copy.** `Machines/ARMReach.lean:197–231` `arm_reach` inlines the guarded-run composition of
`DblLang.Rch.trans` (`Machines/DblLang.lean:116–124`): the endpoint equation, the time split and
the translated second segment (round 2's R2-1). The screen gives 148 of `Rch.trans`'s 202 body
characters (A>B 148/202). Round 3 classifies the pair **G, family K18, group A2a** (ARM-2 (a)) and
counts `arm_reach` whole: 34 code lines, 698 body characters, 148 shared. It is the only counted
declaration of `ARMReach.lean`, which is therefore past one fifth on one measure only, whole-body
code lines: 34 of 158 = **21.5%** (17.6% by whole-body characters, 3.7% and 4.6% by shared text).
These figures are the same at the base, the landed tree and the tip (ledger log).

**Why it is not removed.** The user (2026-10-14; backlog §1 ARM-1, "Clearance with Hydroxyi"):
removing it needs a generic guarded-run composition lemma over an iterated step function, which
`arm_reach` and `Rch.trans` would both cite and which `MReach`/`AReach` (the rest of K18) would
join later. That lemma is the interface design of ARM-2's reachability kit, and interface design
waits for Hydroxyi. So R2-1 stays open on this one copy until he decides, or until the user
acknowledges it in the meantime. The other R2-1 copy, `halvCount_loop` (L049), **is removed** by the
payback (below).

**Named payback.** ARM-2 (a), family K18: the reachability kit (`Rch.trans`, `arm_reach`,
`MReach.trans`/`single`/`mono`, `AReach.*`), designed with Hydroxyi before any brief; owner the user;
not scheduled; a PR plus its gate (zone rules).

**Question 1.** Can the gate close with L066 recorded as acknowledged debt (ARM-2 (a), K18, waiting
for Hydroxyi's generic lemma), or must R2-1 stay open until that lemma lands and `arm_reach` cites
it? If it can close, say what the record must contain; the block below is the proposed form.

### Acknowledgement of L066 (the user's)

> **L066, `arm_reach` ~ `DblLang.Rch.trans`, is recorded as acknowledged debt:** class G, family
> K18, group ARM-2 (a); counted in this ledger (34 code lines, 698 body characters, 148 shared;
> `ARMReach.lean` at 21.5% by whole-body code lines). It stays until ARM-2 (a)'s generic
> guarded-run composition lemma, designed with Hydroxyi, lands; `arm_reach` and `Rch.trans` then
> cite it.
>
> *Entered by the builder from the maintainer's round-3 instructions (the user's decision of
> 2026-10-14, backlog §1 ARM-1: "`arm_reach` waits for Hydroxyi"). The backlog row reads "until he
> decides, or until the user acknowledges it in the meantime"; the user confirms this wording before
> dispatch.*

## What changed since round 2 (MEASURED, provenance log)

- **Records.** The maintainer's records commit applied R2-2 (the §14 registry rows H7–H13) and R2-6
  (the record corrections); locations in the records log.
- **The trees measured.** Every full hash is in the provenance log, from `git rev-parse`.
  - **Base** `ff4cab18`: the merged tip on which the payback was built. Its Lean files equal
    `c9cc485b`'s (asserted). Its Lean differs from round 2's `e831b5b0` in 54 files, by the merges of
    #92 (the B6 hosts), #93 (the minor fixes: comments and imports) and #94–#97.
  - **Landed**: the base plus the payback's 27 patches (`payback/patches/`). Applying them to the
    base export gives the landing folder's tree byte for byte (0 differences).
  - **PR #101** (merge `9c0ae906`, commit `56716442`, first parent `c1ae37d6`) changes exactly those
    27 files, and its 27 files equal the measured landed tree byte for byte. The landing was re-run
    on `eb750e63` (after MIG-1 S, #98) before it merged; the 27 files are identical at
    `ff4cab18`, `eb750e63` and `c1ae37d6`, so the patches and every landed-tree count apply to
    either base.
  - **Tip** `3648415c`. Its 27 payback files equal the landed tree. Ten other Lean files differ:
    eight from MIG-1 S (#98: `ClassP/TimeConstructible`, `TuringMachine/Build/{Catalog,Loop,
    Primitives,Wrappers}`, `TuringMachine/{Composition,Encoding,Simulation}`), all in the screen
    population, none bundled; and #99's `Build/WindowRun` and #100's `TimeHierarchy/Diagonal`,
    outside the population. A third v3 screen at the tip measures their effect: the
    pairs with an added side are the landed tree's 314, with the same hits and classes, and K+ is the
    same 142 rows (ledger log, `tipcompare.py`). Every landed-tree figure in this pack holds at the
    tip; only line numbers in the eight #98 files move.
  - **After the bundle's tip.** The remote branch had moved to `d32e12c0` (#102, U2's statements)
    when this pack was built; its objects are in the local store (from the builder's one
    `git fetch --dry-run`, which changed no ref), not in the local branch ref. It changes five Lean
    files, none in the screen population or the bundle.
- **The screen.** Copy-text screen **v3** (`audits/evidence/retrofit/copy-text-screen-v3.py`,
  committed in `1d76a01a`; notes `audits/evidence/screenfix/v3/NOTES.md`), unmodified, run once at
  each of the three trees over the same 218-file population: round 1's 214 files, two modules now in
  the added files' closure at the base, and two the payback brings into it (provenance log,
  `popcheck.py`). Round 2 ran v1 on flattened copies; v3 keys files by path and declarations by
  path and position, so no copies are needed.
- **v3 reproduces round 2 at the base** (pairs log): the same 353 pairs (120 library, 103 internal,
  130 same-file) from the same 512 directed hits, with the same ids, names and hits, and the same
  body sizes but one. Line numbers moved in 113 pairs (comment edits, mostly #93); the code-line count changed on 9 copy
  sides and 9 source sides, with the bodies unchanged (ESTIMATE: #93's re-wrapped long lines); one
  library body changed (`ConfigGraph.s1b_record_eq_iff`, L062, by #92).
  Round 3's K+ at the base is round 2's acknowledged A4+ (163 declarations) plus exactly the named
  round-3 changes: 9 declarations enter, 2 leave, one changes group, and 9 rows change only their
  code-line count by 1–3 (#93's wraps) (ledger log, `r2decls.py`).

## Round 2's findings: round-3 status

| # | Severity | Round 2's finding (short) | Round 3 | Status |
|---|---|---|---|---|
| R2-1 | major | Two exclusions were genuine copies: `arm_reach` (L066) inlines `DblLang.Rch.trans`'s guarded run composition (`ARMReach.lean` at 21.52% by whole-declaration code lines); `halvCount_loop` (L049) re-proves `InputAccess.access_width_half` | **L049 removed** by the payback: `access_width_half` is public and `halvCount_loop` cites it (`Codec/Engine.lean:244–295` at the landed tree, the citation at line 269; `Logspace/InputAccess.lean:993`); the pair is absent from the landed screen. **L066 not removed** (the user's decision, above): reclassified G, K18, ARM-2 (a), and counted | L049: closed (removed). **L066: open, acknowledged debt; question 1** |
| R2-2 | major | H7–H13 not installed in design §14; H1/H4 named superseded routes | Installed by the maintainer's records commit: `machine-library-design.md` §14 rows H7–H13 (lines 3082–3088 at the tip), the accepted-exception and gate-before-reuse paragraph (3094–3099), `vword_whole₁`'s corrected line (3093); H1, H3, H4, H6 reconciled (3076–3081) | Done (records); **to verify** (point 6). Two rows predate #101 (below) |
| R2-3 | minor | Below-floor members of acknowledged families (`sbI`/`hvI`, `MReach.single`/`mono`); the S072–S074 preimage-oracle pairs | Four manual rows **M3** (K1 ×2, ARM-2 (b); K18 ×2, ARM-2 (a)), tiled by `manualtile3.py`; S072–S074 reclassified G, K2, ARM-2 (b), all three declarations counted (each is the copy side of a directed hit). The copy-side convention is stated below. Totals rerun | Done |
| R2-4 | minor | I082, I083 false-positive G overrides | Reclassified N, X; K2's counts corrected. The copy sides of their two hits, `ARMWidthExample.searchLang_mem_PSPACE` and `SavitchARM/Correct.NSPACE_poly_subset_PSPACE`, stay counted through their genuine length-oracle pairs (I012/I084 and I013/I085 at the base), with the same sizes and shares, so no total moves by these two alone | Done |
| R2-5 | minor | "Cite" impossible as written for I032 and I040; I064's relations differ | Lower homes named and checked on the landed import graph (homes log; next sections): I032 in `ConfigGraph`, I040 in `Codec/Parse`, I064's encoded query in `Logspace/InputAccess`, with the slot and result view at the use sites | Done (text); the factorings themselves are ARM-2 (b) |
| R2-6 | minor | Record corrections still proposals | Applied by the maintainer's records commit: plan row B2 (plan line 855), backlog MIG-19/MIG-22 closed as moot (836, 839), design §12.8's S1b row annotated as historical (1431), §16b on #92's merged status (3858), the `[Bon26]` note (858, 863), the historical probes annotated in the round-2 resolutions (54–57) | Done (records); **to verify** (point 6) |
| R2-7 | minor | Full-path screen key and the older-screen review deferred; 421,911 unlabelled | v2 keys files by repository path, v3 also declarations by path and position (settles the key; this round uses v3 for all three screens, the base re-run included). The older-screen review is recorded: `audits/evidence/screenfix/NOTES.md` (v2: 57 earlier populations, no recorded result needs a correction) and `screenfix/v3/NOTES.md` (at `ff4cab18` the only pair v3 adds is CfgRecord's instance pair, already recorded). This pack labels 421,911 "screen-eligible body characters" and reports 439,027 "all body characters" beside it (414,200 and 431,349 at the landed tree) | Done |
| R2-8 | minor | #93 changed 32 added files and the existing facade, not "33 of the 73"; finding 11's two facade lines deferred | Corrected wording below. The facade's two lines, the three missing sketches and the misplaced `predB_iff` entry landed in #101 (leftovers log) | Done |

Round-1 findings: 1–4 were held by R2-1's joint scope condition, so they close with R2-1 except for
L066, which question 1 decides; 5 closes with R2-2; 8, 9 and 11 close with R2-6, R2-7 and R2-8.

## The payback: the refactor's diff (PR #101)

- **Diff.** `payback/patches/*.patch`, one per file, 27 files: 23 code changes and 4 comment-only
  (`ClassPSPACE/TQBFHardMachine`, `ClassPSPACE/TQBFHardVerifier`, the `SpaceComplexity` facade,
  `ExpBFS/Run`; comment-stripped identity, provenance log). Git: +539 −1,549, net −1,010 lines;
  `r3/patch-stats.txt` per file. The patches are the merged diff: they reproduce #101's 27 files byte
  for byte.
- **What it does** (`payback/LANDING-NOTES.md` §2, the maintainer's account; MEASURED here only
  through the identity checks and the screen):
  - D1: `Turing.Cfg.InWindow` everywhere; Codec's `InWin`, ConfigGraph's private `InWindow` and its
    bridge deleted (and TQBF's private `codec_core_window`, via the new public
    `Cfg.InWindow.core_bounds`);
  - D2, D2h, D3, D5: ConfigGraph's originals made public (D2 and D5 restated with `Cfg.InWindow`);
    the copies in `Codec/Bridge` and `ExpBFS/Radius` deleted; D3's step factored out as
    `FinNDTM.DecidesInSpace.mem_of_acceptsWithin`; ConfigGraph's dead `s1b_*` block deleted;
  - D4 (extended by the user): two visibility changes in `CircuitComplexity/DAGCircuitSat`, the only
    edits there; `TQBFHardTseitin`'s copy deleted, `toCNF_extension_iff` cites both;
  - D6: `TQBF.lean`'s 45 private `b4m*` declarations deleted; `TQBFARM/Semantics`' public twins
    stay as the single home;
  - D7 and `decChain`: one chain lemma `arm_chain` and one stride decoder
    `boundedDecodeStride_loop` in `Logspace/InputAccess`, with `arm_increments`, `incChain`,
    `decChain`, `boundedDecode_loop` and `decodeStride_loop` as instances;
  - L049: `access_width_half` public, cited by `halvCount_loop`;
  - `length_lbStep`: the shared `length_pairEncode_drop_le` (`ClassNP/PolyTimeBlockLoop`);
  - P1+: G-oracle (`indicator_inputBitLang`/`indicator_inputLenLang`), G-canon (`drop_canon` moved
    down to InputAccess), G-outsum, G-prefix, G-tseitin, G-pairidx (`pairEncode_getD_snd`), M2
    (`VWord.getD_drop` cites `List.getD_drop`);
  - the documentation leftovers (R2-8).
- **Public API delta** (`payback/work/api-delta.json`; LANDING-NOTES §4): 28 D1 restatements of
  existing public declarations, each the token rewrite; 20 public additions (9 made public in place,
  11 new or moved in); 7 public removals, all in Hydroxyi's files, with no stale use.
- **Landing evidence** (the maintainer's execution claims, not re-run here): `payback/logs/verify.log`
  60 of 60 at `eb750e63`, including elaboration of every touched module and its named consumers,
  axioms (990 declarations, the standard three, no new `sorryAx`), a 38-module facade cut that
  fails identically before and after (an artifact control), negative controls, and the
  `CircuitComplexity` freeze; the replay of 119 of 119 modules and the snapshot are recorded in the
  backlog (ARM-1, "Landed").
- **Clearance.** The mechanical edits in Hydroxyi's files were an FYI; D4's two visibility changes
  are the user's one-time exception to the `CircuitComplexity/*` rule (backlog ARM-1).

**Dispositions** (`payback/ledger-map.md`, 39 rows: 35 pair rows with L049, and 4 manual rows;
`r3/ledger-r3-tables.md` §2 adds each row's base and landed screen verdict):

| Outcome | Rows |
|---|---|
| Pair absent from the landed screen (copy deleted, moved, or re-pointed with the shared text gone) | 27: S030, L003–L006, L009–L012, L016, L017, L024, L025, L038–L043, L045–L047, L049, L050, L052, L054, L055 |
| Pair still on the screen, both sides now citing the shared declaration (re-classified N, X at the landed tree; `r3/landed-overrides.tsv`) | 5: L001, L002, L056, L057 (G-oracle), L048 (D7's stride-1 instance) |
| Kept by the user's dispositions | 3: L033 (G-rep, ARM-2 and the dedup window, A2w), L119 and L120 (G-vword, not real duplication) |
| Manual rows | D1 `InWin` and D5 `inWin_of_coreSum_eq` deleted; D6 `synOK` kept as the single home (`b4mValid` deleted); M2 re-pointed |

The seven D6 twins (six screen pairs and the manual row `synOK`) keep `TQBFARM/Semantics` as the
single home.

## The ledger, re-measured (MEASURED screen; classification by the pack's author)

**Method.** `scripts/pairs3.py` turns each v3 output into unordered pairs with an added side and
maps them to round 2's ids by (category, both `path::name`). `scripts/classify3.py` carries round
2's class, family and group for every round-2 id (acknowledged), applies the named round-3 changes
(table below), classifies new internal and same-file pairs by round 2's rule, and new library pairs
from the inspected table `r3/n3lib.tsv`; at the landed tree and the tip it also applies
`r3/landed-overrides.tsv` (pairs the payback re-pointed). `scripts/manualtile3.py` measures the
manual rows on each tree; `scripts/ledger3.py` computes the accountings. Measures and conventions
are round 2's: a declaration counts once, whole, if it is the copy side of a counted pair; whole
body (characters, code lines) and shared text (the largest single overlap, capped at the body; code
lines prorated).

**Round-3 classification changes** (each from a round-2 finding or a user decision):

| Pair | Copy ~ original | Round 2 | Round 3 | Basis |
|---|---|---|---|---|
| L066 | `Machines/ARMReach.arm_reach` ~ `Machines/DblLang.Rch.trans` | N, X | G, K18, A2a | R2-1; open, acknowledged debt |
| L049 | `Codec/Engine.halvCount_loop` ~ `Logspace/InputAccess.access_width_half` | N, X | G, G-halfwidth, P1 | R2-1; removed by the payback |
| S072–S074 | `Logspace/PathHardRegs.orc_init`/`orc_acc`/`orc_step` | N, X | G, K2, A2b | R2-3: one parameterized preimage-answer lemma |
| I082, I083 | `PathHardRegs.orc_bit` ~ `ARMWidthExample.searchLang_mem_PSPACE`, `SavitchARM/Correct.NSPACE_poly_subset_PSPACE` | G, A2b | N, X | R2-4: false positives |
| L033 | `ClassPSPACE/TQBFHardVerifier.pt_rep_mul` ~ `CookLevin/Hardness.clA5Times_native` (private) | G, P1+ | G, G-rep, A2w | user 2026-10-14: ARM-2 and the dedup window, with a home decision |
| L119, L120 | `Machines/VWord.vword_whole₂`/`₃` ~ `Logspace/InputAccess.vword_whole₁` | G, P1+ | N, X | user 2026-10-14: not real duplication |

**Pair inventory** (pairs and transitions logs; `r3/transitions.tsv`):

| Category | Base | Landed | At both | Removed by the payback | New at the landed tree |
|---|---:|---:|---:|---:|---:|
| Library | 120 | 94 | 85 | 35 | 9 |
| Internal | 103 | 93 | 93 | 10 | 0 |
| Same-file | 130 | 127 | 127 | 3 | 0 |
| **Total** | **353** | **314** | **305** | **48** | **9** |

The 48 removed pairs by base group: P1 19, P1+ 8, A2b 7, X 14. The A2b seven are K2's input-length
oracle pairs I009–I013, I042, I043, whose `TQBFARM/Machine.orc_len` and `Codec/Run.orc_len` side now
cites the public `indicator_inputLenLang`; the other five length-oracle provers now pair with that
public lemma instead (**L3-005–L3-009**, G, K2, A2b; inspected, `r3/n3lib.tsv`). The other four new
pairs (**L3-001–L3-004**) are re-pointed wrappers sharing only the citation (N, X). Present at both
trees with a group change: P1 → X one (L048), P1+ → X four (L001, L002, L056, L057). Two internal
G pairs re-pointed by G-oracle stay counted (I005, I008: two identical per-machine wrappers, both
now citing the public lemma; ARM-2 (b)'s shared bank removes them).

**Pairs by group** (classify log): round 2 P1 19, P1+ 15, A2a 25, A2b 117, X 177; round 3 at the
base P1 20, P1+ 12, A2a 26, A2w 1, A2b 118, X 176 (the named changes: L049 and L066 out of X, S072–S074
into A2b, I082 and I083 into X, L033 to A2w, L119 and L120 to X); at the landed tree A2a 26, A2w 1,
A2b 116, X 171, and no P1 or P1+ pair.

**Totals** (ledger log; `r3/ledger-r3-tables.md` §4). Denominators: base 17,268 code lines,
421,911 screen-eligible body characters (declarations with a body of at least 60 whitespace-free
characters), 439,027 body characters in all; landed 17,017, 414,200 and 431,349.

| Accounting | Tree | Declarations | Whole body: code lines | Whole body: chars (/eligible; /all) | Shared text: chars (/eligible; /all) | Shared text: code lines |
|---|---|---:|---:|---:|---:|---:|
| C, every candidate | base | 242 | 5,657 (32.8%) | 163,343 (38.7%; 37.2%) | 73,896 (17.5%; 16.8%) | 2,714 (15.7%) |
| C | landed | 218 | 5,241 (30.8%) | 152,089 (36.7%; 35.3%) | 65,685 (15.9%; 15.2%) | 2,412 (14.2%) |
| K, N excluded | base | 152 | 4,081 (23.6%) | 119,740 (28.4%; 27.3%) | 64,477 (15.3%; 14.7%) | 2,304 (13.3%) |
| K | landed | 128 | 3,641 (21.4%) | 108,433 (26.2%; 25.1%) | 56,180 (13.6%; 13.0%) | 1,981 (11.6%) |
| **K+, with the manual rows** | base | 170 | 4,135 (23.9%) | 120,796 (28.6%; 27.5%) | 65,061 (15.4%; 14.8%) | 2,338 (13.5%) |
| **K+** | **landed** | **142** | **3,682 (21.6%)** | **109,249 (26.4%; 25.3%)** | **56,650 (13.7%; 13.1%)** | **2,010 (11.8%)** |

Round 2's acknowledged A4+ was 163 declarations and 15.3% by shared text. C at the base equals
round 2's A2 in characters (163,343 and 73,896); its code lines are 15 higher (#93's wraps).

**K+ by group at the landed tree:** no P1 or P1+ declaration remains. A2a 13 declarations (301 code
lines, 8,050 body characters, 2,498 shared), including `arm_reach`; A2w 1 (`pt_rep_mul`: 10, 179,
66); A2b 128 (3,371, 101,020, 54,086). At the base: P1 21, P1+ 11, A2a 13, A2w 1, A2b 124.

**Files past one fifth** (K+; `r3/ledger-r3-tables.md` §5–6, both measures and both units):

| Measure | Base | Landed | No longer past at the landed tree |
|---|---:|---:|---|
| whole body, chars / screen-eligible | 33 | 28 | `ClassPSPACE/TQBFARM/Semantics`, `Codec/Engine`, `ClassPSPACE/TQBFHardTseitin`, `ClassPSPACE/TQBFHardSemantics`, `ClassPSPACE/TQBFARM/Machine` |
| whole body, chars / all body | 31 | 28 | `Codec/Engine`, `ClassPSPACE/TQBFHardTseitin`, `ClassPSPACE/TQBFARM/Semantics` |
| whole body, code lines | 30 | 26 | `Codec/Engine`, `ClassPSPACE/TQBFHardTseitin`, `ClassPSPACE/TQBFARM/Semantics`, `ClassPSPACE/TQBFHardSemantics` |
| shared text, chars / screen-eligible | 21 | 17 | `ClassPSPACE/TQBFARM/Semantics`, `Codec/Engine`, `Codec/Bridge`, `ClassPSPACE/TQBFHardTseitin` |
| shared text, chars / all body | 20 | 16 | the same four |
| shared text, code lines (prorated) | 16 | 12 | the same four |

No file is newly past one fifth at the landed tree. `Machines/ARMReach.lean` is past on whole-body
code lines at both trees, by L066 alone.

**At the tip** (`r3/ledger-r3-tables.md` §8): the same 314 pairs, classes, totals, groups and
one-fifth lists as at the landed tree, and K+'s 142 rows identical in everything but line numbers.
#98 adds library declarations (the screen reads 5,081 declarations and 4,906 directed hits at the
tip against 5,053 and 4,835 at the landed tree), but none of the new hits has an added side.

## R2-3 and R2-4: the corrections

- **M3 manual rows** (`r3/manual3-spec.tsv`; measured `r3/manual3-base.tsv`, `-landed.tsv`,
  `-tip.tsv`): `SavitchARM/Machine.sbI` and `hvI` against `TQBFARM/Machine.sbI`/`hvI` (bodies 57 and
  58, wholly shared; K1, A2b); `Machines/MARM.MReach.single`/`mono` against
  `Machines/ARMProof.AReach.single`/`mono` (47 and 49 shared; K18, A2a).
- **The copy-side convention.** Against a library declaration, the added declaration is the copy
  (round 2's rule; `ARMProof` is library code). Between two added files, a manual row counts one
  side, as round 2's M1 rows do, with `TQBFARM/Machine` as the original, as in M1 (neither machine
  file imports the other). The screen's own rule counts both sides of a mutual hit; applied here it
  would add `TQBFARM/Machine.sbI` and `hvI`: 2 declarations, 10 code lines, 115 body characters.
- **S072–S074** (`PathHardRegs.orc_init`, `orc_acc`, `orc_step`): G, K2, A2b. The factoring is one
  lemma for the preimage oracle's answer at a decider index, of which the three are instances.
- **I082, I083**: N, X. Round 2's K2 pairs I012, I013, I057, I084 and I085 (the real length-oracle
  pairs) are unchanged at the base; at the landed tree I012 and I013 are re-anchored to the public
  `indicator_inputLenLang` (L3-008, L3-009), still G, K2, A2b.

## R2-5: the lower homes (homes log; ESTIMATE that the moved text elaborates in its home)

Checked on the landed tree's import graph (`scripts/imports.py`, `scripts/homes.py`); all checks
pass, and pass again at the tip.

| Pair | Why "cite" fails as round 2 wrote it | The home | The factoring |
|---|---|---|---|
| I032 (K9) `Codec/Bridge.mem_iff_codeChain` ~ `ExpBFS/Radius.inWin_runWith_of_decides` | `Radius` imports `Bridge` | `SpaceComplexity/ConfigGraph`, imported by both, beside `NDTM.runWith_take_inWindow` and `FinNDTM.DecidesInSpace.mem_of_acceptsWithin` (both public there since #101) | Move the window lemma (a space-bounded decider's every branch stays in `Cfg.InWindow (sp x.length)`) to ConfigGraph; Bridge's proof and Radius cite it. Its citations (`runWith_take_inWindow`; `NDTM.runWith_append`, `runWith_of_halt` from `TuringMachine/Nondeterministic`) are at or below ConfigGraph |
| I040 (K20) `Codec/Layout.two_pow_bits_le` ~ `Codec/Parse.bitsVal_le_of_width` | `Layout` imports `Parse` | `Codec/Parse` | Move `two_pow_bits_le` into Parse before `bitsVal_le_of_width`, which cites it; Layout keeps it through its import |
| I064 (K20) `ExpBFS/Relax.stp` ~ `SavitchARM/Recursion.Rel` | Neither imports the other; `Relax` imports no `Codec` module, so a Codec home is not below it | `Logspace/InputAccess`, imported by `Relax`, `Recursion` and `PathHardRegs` (the third builder of the same query); `pairEncode` is defined below it (`TuringMachine/Encoding`) | Factor only the encoded query `⟨x, ⟨bits u, ⟨bits v, bits r⟩⟩⟩`; the slot (2 in `Relax`, 3 in `Recursion`, 4 in `PathHardRegs.orc_step`, which nests `⟨x, β⟩`) and the result view (`Bool`, or `= true`) stay at the use sites. The G class covers the repeated query, not equality of the two oracle relations |

## R2-7: labels and the screen

Every character percentage in this pack and in `r3/ledger-r3-tables.md` gives both denominators:
"screen-eligible body characters" (bodies of at least 60 whitespace-free characters: 421,911 at the
base, 414,200 at the landed tree) and "all body characters" (439,027; 431,349). The acknowledged
15.3% is of the screen-eligible denominator, and it is not a fraction of all received source text.
Manual rows below the floor enter the numerators only (round 2's convention, kept).

## R2-8: the corrected wording

- **PR #93** changed comments and imports only, in **32 of the 73 added files and in the existing
  `ClassPSPACE.lean` facade** (33 files in all), not "33 of the 73 added files".
- **Round-1 finding 11** was fixed in part by #93: the 42 long lines, the 15 headings and the two
  quantifier-block sketches in added files. The rest landed in #101, comment-only (leftovers log):
  the `SpaceComplexity` facade's two Contents lines over 100 columns (lines 228 and 234 at the base,
  101 and 146 columns; none over 100 at the landed tree); proof sketches for
  `numVars_le_length_serialize` (`ClassPSPACE/TQBFHardTseitin.lean:113`), `reflTransGen_stepRel`
  (`ClassPSPACE/TQBFHardMachine.lean:105`) and `nz_run` (`ExpBFS/Run.lean:607`); and
  `TQBFHardVerifier`'s Main-results bullet for `predB_iff` (line 55 at the base) removed, with the
  prose naming its home `TQBFHardBridge` (whose bullet, line 31, stays).

## The 25 absent counterparts, and L033 (`r3/excerpts-n-pairs.md`)

Round 2 could not show the library side of 25 N-class pairs (L013, L014, L036, L037, L063,
L088, L089, L094–L109, L112 and L113). Each excerpt gives
both ends with `file:lines` at the base, the screen's shared tiles for the pair's largest directed
hit (recomputed by the screen's own greedy tiling, blocks of at least 25 whitespace-free
characters), and the library declaration's whole raw span, numbered. L033's counterpart
(`CookLevin/Hardness.lean`, 470 KB, not bundled) is excerpted the same way. Of the excerpted files,
`Build/Catalog` (L013), `Build/Loop` (L014, L096) and `TuringMachine/Encoding` (L097) changed at the
tip (#98): the four spans moved (Catalog 6235 → 6317; Loop 340 → 352 and 3153 → 3376; Encoding
353 → 364) with their hits unchanged; each excerpt gives its tip lines.

## Records at the tip (records log)

The R2-2 and R2-6 locations are in the status table. Two §14 rows predate #101 and still describe
its items as future work: H10 lists `InWin` and says it "retires into `Turing.Cfg.InWindow` in the
payback PR" (line 3085); H11 says of D7 and `decChain` "(decided)" (3086). The backlog's ARM-1 row
gives the payback as "net −938 lines" (line 756); git gives net −1,010 (+539 −1,549). These are the
maintainer's to update; no ledger figure depends on them.

## Brief for the auditor

Points to rule on:

1. **L066** (question 1 above): can the gate close with it recorded as acknowledged debt, or must
   R2-1 stay open until ARM-2 (a)'s lemma lands?
2. **The re-measured ledger.** Rerun the scripts (`NOTES.md`). Check that:
   - the base screen reproduces round 2's inventory, and K+ at the base is round 2's A4+ plus
     exactly the named round-3 changes (pairs and ledger logs);
   - the landed inventory and the 48 removals and 9 additions follow from the landed screen, and
     every pair present at both keeps its round-2 class except the named changes and overrides;
   - the seven landed overrides (`r3/landed-overrides.tsv`) are right. Challenge in particular the
     line between L001/L002/L056/L057 (re-classified N: the shared text is the citation) and
     I005/I008 (kept G: two identical per-machine wrappers);
   - the nine inspected new library pairs (`r3/n3lib.tsv`) are right, and L3-005–L3-009 stay A2b
     (not payback rows missed);
   - the totals, the group split and the one-fifth lists follow from the per-file table;
   - the tip ledger is the landed tree's (`tipcompare.py`), so #98–#100 change nothing here.
3. **The payback against the ledger** (the refactor's diff). For each of the 39 ledger-map rows,
   does the patch do what the map says, and is the landed screen verdict consistent with it? Does the
   diff introduce any new copy (the landed screen's new pairs are the nine above)? Is the public API
   delta exact (28 D1 restatements as token rewrites; 20 additions; 7 removals with no stale use;
   `payback/work/api-delta.json`, `payback/logs/freeze.log`)? The backlog's ARM-1 row says the
   payback "changes public statements (D1), so it gets a full gate"; **rule whether this round's
   review of the delta discharges that, or a separate statement gate is needed.**
4. **R2-5's homes**: is each home importable by every user, and does each factoring preserve the
   users' statements?
5. **The corrections** (R2-3, R2-4, R2-7, R2-8): exact as stated?
6. **The records** (R2-2, R2-6): are H7–H13 and the reconciliations in §14 as round 2 required, and
   are the R2-6 corrections applied as resolved? Note the two rows that predate #101.
7. **The excerpts**: do they support every N classification of the 25 pairs, and L033's G?
8. **Adversarial checks** (at least six), for example:
   - a payback re-point that leaves a second proof of the same fact elsewhere in the added files;
   - a removed pair whose copy survives under a new name (search the landed screen by body);
   - a landed override hiding a real argument;
   - a file whose one-fifth status depends on the eligible versus all-body denominator;
   - a P1 or P1+ row whose original is private in a colleague's file and was changed without
     clearance (only D4's two visibility changes are cleared);
   - a manual row whose landed measurement is stale;
   - an R2-5 home that creates an import cycle.
9. Report anything else this pack, `NOTES.md` or `r3/ledger-r3-tables.md` misstates.

## Repository-side attestations (verify or challenge)

MEASURED = computed by a round-3 script, log attached. ESTIMATE = a judgement or a text-level
check. One runner pass (`r3/scripts/run_r3.zsh`, exit 0).

1. **Environment** (MEASURED). No Lean, no `lake`, no olean written; no elaboration in this round.
   Python as `python3 -I -B`. Git read-only (`rev-parse`, `cat-file`, `show`, `archive`, `diff`,
   `ls-tree`, `merge-base`, `log`), apart from one `git fetch --dry-run`, which updated no ref but
   stored #102's objects. The three screens ran one at a time under `nice -n 10`. Every full hash
   came from `git rev-parse`, and every hash-like token in this pack and `NOTES.md` resolves to a git
   object it prefixes (hashcheck log). Everything was written under the builder's folder and the
   dispatch folder.
2. **Identity** (MEASURED, provenance log): the base export equals `git show` of the base; the base
   plus the 27 patches equals the landed tree and the landing folder's tree; PR #101 changes exactly
   the 27 files, equal to the landed tree; the tip's 27 files are equal too, and no bundled Lean file
   differs between the tip and the landed tree; `land-payback/SHA256SUMS` rechecks.
3. **Screens** (MEASURED): v3 byte-identical to the tip's copy (SHA-256 in the provenance log); the
   population (218 files) and its derivation (`popcheck.py`); the screen logs carry each run's exit
   status, elapsed time, output hash and the added-side hit lines verbatim.
4. **Pairs, classes, ledger** (MEASURED counts; classification ESTIMATE, the pack author's): as
   tabled; the base comparison with round 2 (`r2compare.py`, `r2decls.py`).
5. **The payback's landing evidence** (the maintainer's claims, not re-run): verify 60/60 at
   `eb750e63`; the replay of 119 modules; the axiom prints.
6. **R2-5, R2-8, records** (MEASURED text and import-graph checks; homes, leftovers and records
   logs).
7. **Not established here:** any Lean elaboration; a semantic (not textual) duplication search; the
   classification beyond the stated rule and inspection; the population files outside the bundle
   (excerpted where a counted or questioned pair needs them).

## Bundle

The bundle's sections are the repository paths, in this order (`r3/BUNDLE-FILES.txt` lists them
with sizes):
1. this pack; round 2's findings, resolutions and pack; round 1's findings;
2. the standards: `audits/TEMPLATE.md`, `policy.md`, `workflow.md`;
3. the response, the backlog, the design document and the plan, whole, at the tip;
4. round 3's notes, evidence and scripts (`r3/`), and its 13 logs;
5. the payback's landing material (`r3/payback/`): the landing notes, the ledger map, the replay
   order, `SHA256SUMS`, the 27 patches, 11 logs, the API delta and 17 scripts;
6. the round-2 evidence the scripts read (`r2/pairs.tsv`, `classify.tsv`, `kfam.tsv`, `manual.tsv`,
   `ledger2-decls.tsv`, `ledger-r2-tables.md`, `registry-rows.md`, `corrections.md`), round 1's
   population labels and the added-file list, the v3 screen and the two screen-fix notes;
7. the 73 added files and the 27 library files that the ledger rows, the payback and the registry
   cite, at the tip (the 27 payback files among them equal the measured landed tree).

243 files, about 5.0 MB. Not included: the landing folder's `tree/` (equal to the bundled tip files), the
population files outside the 100 bundled (excerpted where a counted or questioned pair needs
them), and the immutable round-1 and round-2 bundles (dispatch folders 18 and 21).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (debt: failure mode 5). Findings go verbatim into
`audits/arm-extensions-fill-r3-findings.md`. The gate closes when this round reports zero blockers
and zero majors, with the user's acknowledgement recorded for any duplication that remains.
