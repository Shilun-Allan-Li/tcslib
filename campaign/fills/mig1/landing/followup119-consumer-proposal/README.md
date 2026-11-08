# API119 consumer adoption proposal

**Proposal complete; actual source remains unchanged.** The definitive expanded proposal is
[`generation2/all15-bodies.patch`](generation2/all15-bodies.patch), pinned to clean MIG head
`b1f553b315f31b949076e91119473ce4070e7d53`. It contains twelve least-entry reuses, two Catalog
zero-space fact reuses and deletion of the exact Catalog redirection block already supplied by
API119's Wrappers owner. These are fifteen scoped changes in six files: fourteen proof-body
changes (eleven private, three public) and one staged owner adoption. No surviving declaration
header, visibility, relative order, import, attribute, machine/type/data/instance definition or
runtime field changes. No new public or private declaration is proposed.

Prerequisite: gate119 closes and Seyoon merges #234. Root must integrate the complete merged
API source before applying the scoped hunks. The saved whole-file `.lean.txt` copies are
**b1-relative review artifacts; do not overwrite integrated files with them**. They deliberately
do not synthesize a merge and therefore omit API119 publisher additions present only in that PR.
The proposed Catalog deletion preserves the global public name through its new Wrappers owner.

## Evidence and limits

The frozen native generation 1 (`generation1-manifest.json`, `generation1-note.md`,
`verification.json`) tested the exact three private wrapper headers and the two new zero-space
leaf expressions against complete read-only `oleans-mfollowup-preflight`, pinned Lean 4.25.0.
Native and strong sealed consumers both passed with zero errors and warnings. Five roots and
two compiled proof descendants use only `propext`, `Classical.choice`, `Quot.sound`.

All six ordinary foreign TCSlib definitions found in those proof terms and types were sealed
before the complete headers and bodies. `Cfg.init` was conservatively sealed too; the default
simp entries `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg` were removed. The four excluded
entries are actual compiled projection abbreviations, listed in `verification.json`. The only
explicit named rewrite arguments are the two published zero-space theorem facts.

The same fourteen control identities each pass native `rfl` with a kernel-checked declaration
and fail sealed `rfl` as intended: pointwise data projection and complete abstract defining
function for each of seven definitions. Exact identities/multiplicities and four synthetic
missing/duplicate-marker corruptions were checked. `Controls-sealed` exits 1 with exactly
fourteen retained expected failures; it is negative instrumentation evidence. There were no
unexpected failed Lean attempts. The first native consumer's 242.91 seconds includes managed
slot waiting and is not a pure elaboration timing.

**Generation 2 is source-only.** Its nine additional production-body rewrites, including
`emCall_eval_first`, were not elaborated. The original two Catalog *leaves* were checked;
the full existential/computation rows were not. No full proposed MIG module, integrated
12-module chain, merged-tree replay, copy screen or global compiled census was run for this
proposal. The complete legacy remainder of newly touched inline bodies still contains foreign
reader/unfolding sites; actual integration must perform its strong region seals, argument
inspection and routine published-reader repair without claiming this packet already did so.

`generation2/freeze.json` independently reconciles the exact patch in memory against all twelve
captured current MIG sources, uses the reviewed balanced full-header reader with statement-let
and proof-valued-let controls, and verifies byte-identical non-target source/runtime material.
All seventeen filled targets remain filled with unchanged headers, and the three residual RAM
admissions retain their literal proof bodies. Generation 1's input/output hashes remain frozen.
The actual worktree HEAD, all twelve Lean source bytes and clean Lean index were checked again.

## Proposal contents

| Artifact | Role |
| --- | --- |
| `generation2/all15-bodies.patch` | Definitive fifteen scoped changes, relative to b1 |
| `generation2/inputs/*-{before,after}.lean.txt` | Exact reviewed declaration/local body contexts |
| `generation2/inputs/*-after15-b1-REQUIRES-INTEGRATED-API119.lean.txt` | Inert complete baseline-relative source copies |
| `generation2/optional-sketches-after-bodies.patch` | Optional comment-only synchronization for fourteen sketches and the Catalog owner index |
| `generation2/receipt.json`, `generation2/freeze.json` | Exact before/after hashes, census, header/runtime/target preservation and validation limits |
| `SWEEP.md`, `sweep-inventory.json` | Bounded twelve-file least-entry/run-absorption classification |
| `Consumers-*`, `Controls-*`, `generation1-manifest.json` | Actual frozen small native/sealed evidence |
| `consumer-bodies.patch`, `seventh-existing-first-halt.patch` | Earlier separately requested six-change/seventh stages, superseded in scope by generation 2 |

The generalized live-stop theorem serves five sites: two predicate wrappers, one singleton
wrapper, `splitEmbed_cut`, and `fwdMap_launch`. Its global fixed-step and live endpoint premises
are retained. The pre-existing NONE-first-halt theorem serves the other seven least-entry sites;
its complete configuration equality transports arbitrary output and fields, including for the
arbitrary starting bank in `splitBody_count`. Deadline inequalities remain analysis bounds;
there is no added native clock, controller, public API, import, statement change or debt ruling.

`SWEEP.md` classifies the remaining matched run/absorption and list-order contexts. It makes no
claim that a source grep proves whole-library factoring closure or that any acknowledged family
has acquired a new status. Root owns later adoption, actual integrated validation and audit
preparation; this records-only proposal grants no gate closure or merge clearance.
