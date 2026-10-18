# NOTES — ARM-extensions fill gate, round 2 (received commit `8c23f3bc`)

Author: maintainer sub-agent. Date: 2026-10-14. Output root: `$S/gate-arm-r2/` (`$S` = the session
scratchpad). Repository mapping when the maintainer lands the round:
- `arm-extensions-fill-r2-pack.md` → `audits/arm-extensions-fill-r2-pack.md`;
- `NOTES.md`, `evidence/*` → `audits/evidence/arm-fill/r2/` (with `evidence/inputs/` →
  `r2/inputs/`, `scripts/*` → `r2/scripts/`);
- `logs/arm-fill-r2-*.log` → `audits/logs/`.

## Ground rules kept

- No edit to the repository or to the checkout `$S/wt-armr2` (HEAD `39bfdca4`, clean). Read-only git
  only: `rev-parse`, `cat-file`, `diff`, `log`, `show`, `grep`, `merge-base`. Every full hash came
  from `git rev-parse`; `logs/arm-fill-r2-hashcheck.log` resolves every hash-like token of the pack,
  these notes, `corrections.md` and `registry-rows.md`.
- No Lean, `lake` or `elan`; no olean produced. Python only as `python3 -I`; shell zsh.
- Everything written under `$S/gate-arm-r2/`. One slip, corrected at once: two temporary file lists
  were first written to `$S/` and moved into `work/` before anything else ran.
- The copy screen was run unmodified, from the checkout, on byte copies under flattened
  path-encoded names (the basename workaround; the v2 tool is not used).

## The session was interrupted (about 16:22 UTC) and resumed

On resuming I re-checked `gate-arm-r2/`: only `work/` and `scripts/` existed, no deliverable had
been written. I then wrote one runner, `scripts/run_r2.zsh`, which regenerates every table and log
from the inputs, and ran it from scratch; the regenerated `pairs.tsv` is byte-identical to the one
made before the stop. All counts in the pack come from the final runner pass.

## Method and results (each with its log)

1. **Provenance** (`arm-fill-r2-provenance.log`). Tip `e831b5b0` (backlog-only since `6fbdefac`;
   Lean tree identical to `39bfdca4`). The 81 received `.lean` files are byte-identical at
   `8c23f3bc`, `733c22b7` and the tip. Digests of round 1's inputs and of this round's two hand
   inputs (`kfam.tsv`, `manual-spec.tsv`).
2. **Drift** (`arm-fill-r2-drift.log`). Of round 1's 214-file population: 202 identical, 3
   comment-only, 9 code changes (C1, MIG-0b). Only two incidental pairs touch a changed file; their
   library lines moved (`Catalog`, `Embed`).
3. **Screen rerun** (`arm-fill-r2-screen-added-only.log`). The 73 added files at the tip: output
   byte-identical to round 1's (772 declarations, 343 pairs); copies' SHA-256 equal round 1's labels.
4. **Pairs** (`arm-fill-r2-pairs.log`; `scripts/pairs.py`). 512 directed hits with an added side
   (169 library, 144 internal, 199 same-file), 353 unordered pairs (120, 103, 130). The screen's
   same-name blind spot inside one file is empty (`scripts/dupnames.py`).
5. **Classification** (`arm-fill-r2-classify.log`; `scripts/classify.py`). Rule plus 26 named
   overrides (7 to N, 19 to G); library pairs by inspection per copy-side declaration. Groups from
   the user's dedup decisions (backlog ARM-1, ARM-2 at `e831b5b0`): P1 19 pairs, P1+ 15, A2a 25,
   A2b 117, X 177. I inspected the shared tiles (`scripts/showpair.py`) of most same-file and
   internal pairs, of at least one pair of every component, and of the largest pair of every
   library copy-side declaration; the rest follow their family. The classes are my judgement.
6. **Ledgers** (`arm-fill-r2-ledger.log`; round 1's `ledger.py`, then `scripts/ledger2.py`).
   Round 1's ledger reproduces byte for byte. A1 151 decls / 25.7% whole-body / 10.1% shared
   (round 1); A2 242 / 38.7% / 17.5% (the round-1 auditor's figure, reproduced, 28 files on shared
   text); A4+ (the ledger for acknowledgement) 163 / 28.0% / 15.3%. Files past one fifth in A4+:
   34 by whole-body characters, 29 by whole-body code lines, 20 by shared characters, 18 by shared
   code lines (prorated).
7. **Families** (`arm-fill-r2-families.log`; `scripts/families.py`). Round 1's 45 internal
   components: 12 substantive, 12 small genuine, 21 incidental. 61 same-file components: 23, 5, 33.
   21 logical families K1–K21 with factorings (`evidence/ledger-r2-tables.md` §4).
8. **Registry inputs** (`arm-fill-r2-registry.log`; `scripts/finddecl.py`, `consumers.py`, round 1's
   `tools/imports.py`). Declaration header lines and direct importers at the tip. Draft rows:
   `evidence/registry-rows.md`.
9. **C1 delta** (`arm-fill-r2-c1delta.log`). PR #87's diff equals `dc891632..733c22b7` byte for byte
   (10 Lean files, blob ids and SHA-256 tabled); two are upstream of the received modules; the two
   C1 lemmas are `sorry` at the received tree and named by no other code there.
10. **Records** (`arm-fill-r2-records.log`). `InWin` 48 code uses in 7 files; the D6 range holds 45
    private `b4m*` declarations; no outside reference to `b4m*` or `s1b_*`.
11. **Comment-only PRs** (`arm-fill-r2-commentonly.log`). #89 (17 files) and #91 (1 file) change
    comments only.
12. **Tables** (`scripts/tables.py` → `evidence/ledger-r2-tables.md`).

## Unexpected findings (recorded in the pack)

1. **The D6 count.** ARM-1 at `e831b5b0` says the `b4m*` appendix (lines 2474–3185) has 44
   declarations; it has **45** (13 `def`, 29 `theorem`, 2 `abbrev`, 1 `structure`), as round 1 also
   counted. The line range and the 712 lines are right.
2. **Below-floor duplication the screen cannot see**: the decider banks restated per machine (M1,
   10 declarations), and `VWord.getD_drop`, a Bool copy of the public `Programs/Util/List.getD_drop`
   outside the screen population (M2).
3. **A semantic duplicate with no text pair:** `ARMWidthExample.d1_loop`/`d2_loop` re-prove
   `ARMLoops.dmove_run`/`move_run`; `ARMLoops` is not in that file's import closure.
4. **Second uses already inside the delivery:** inductive counting imports Savitch's decider bank
   (`ISCountRegs` → `SavitchARM/Correct`) and `ExpBFS`'s stop rule; `ExpBFS/Main` restates
   Savitch's code bank in another order.
5. **`DecidesInSpace.mem_iff_acceptsWithin_configBound` is already public** (`ConfigGraph.lean:533`);
   D3's copy replays its backward branch, so the payback promotes that branch as its own lemma.
6. **The B6 hosts' 2026-10-13 `ConfigGraph` draft patch** edits the `s1b_*` block and lists
   `NSPACE_subset_exp_dtime` among `ConfigGraph`'s main results; both are overtaken (the block is
   dead and the theorem moved). To check against #92 when it is regenerated on the tip.
7. Several screen pairs owe their shared text to declaration spans that run to the next header:
   `section … variable` lines and scoped `macro_rules` (the `regs` macro inside `Bd.toV`'s span).
   The first kind is classified incidental; the second is a real copied macro (K1).

## Open issues for the user and the maintainer

1. **The acknowledgement** (the user's): scope and date, in the pack's placeholder.
2. **The 15 P1+ pairs (13 declarations) and M2**: confirm that they join the payback PR (they are
   copies of campaign code, or ride with D4, which is cleared with Hydroxyi). Two originals are
   private in our files (`QueryReshape.drop_bit`, `drop_canon`), one in `Mult`, one in CookLevin
   (`clA5Times_native`); `toCNF_extension_iff` touches Hydroxyi's DAGCircuitSat with D4.
3. **Finding 12's helper moves** (not in #93): join #93, the payback PR, or ARM-2.
4. **Records to correct** (`evidence/corrections.md`, finding 8): ARM-1's D6 count; plan B2 and the
   fills-6 note; MIG-19 and MIG-22 closed as moot; design §12.8 S1b rows, §16b item 3, §14 H1/H3/H4/H6;
   the historical probes' annotation; the `[Bon26]` history.
5. **#92 and #93**: the auditor needs their diffs to check findings 6, 10, 11 and the B6 patch note;
   the maintainer bundles them when ready.
6. **Bundle**: `evidence/BUNDLE-FILES.txt`, 169 files, about 5.2 MB (`scripts/mkbundle.zsh`); it
   lists repository paths at the tip, and this round's files under their landing paths.
7. **Reproducing from the repository**: `run_r2.zsh` reads round 1's builder folder. Its work files
   that round 1 did not land are copied to `r2/inputs/` (`MANIFEST.txt`, SHA-256); the 214 screen
   copies are the received tree's files named by round 1's labels (SHA-256 checked); the provenance
   check of the combined input also reads round 1's two raw screen outputs, which are its landed
   screen logs without their header lines.
