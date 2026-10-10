# Chapter-7 fill surface — duplication screen (merged tree)

Maintainer pre-screen for the ch7 fill gate's duplication question (pack question 7),
run on the merged tree `complexity/arora-barak-ch3-4` at `49658bb6` under this
repository's duplication governance (`policy.md` **Duplication**, `workflow.md` §4,
`audits/TEMPLATE.md` failure mode 5). The auditor verifies these facts and judges the
classification; it is a starting point, not a substitute for the audit.

## Method

Script: `audits/evidence/ch7/ch7-fill-duplication-screen.py`. Every `.lean` file under
`TCSlib/` (561 files) is comment-stripped and split into declarations. Each of the
**112 declarations** of the six-file surface (`Build/EmitIterEmbed`,
`Build/EmitIterBody`, `ClassNP/PolyTimeBlockLoop`, `PolyTimeBlockTests`,
`PolyTimeBlockMajority`, and the three new `PClosure` headliners) is cut into token
shingles in two modes: **exact** (25-token runs) and **renamed** (50-token runs with
every identifier abstracted, so a consistently renamed copy still matches). A
declaration's overlap is the fraction of its shingles found in one other declaration
anywhere in the tree. Reported threshold: ≥ 50%.

**Coverage qualification.** The screen detects contiguous reproduction, exact or under
consistent renaming. It does not detect re-derivations whose proofs are restructured,
and it says nothing about design-level parallels. Whether `EmitIterEmbed` duplicates
the §12 `Build/Embed` layer is a non-mechanical question for the auditor.

## Results

**Class A: one per-loop lemma set re-proved under renaming (debt).** The OR, XOR and
strict-majority loops each carry their own copy of the same orbit, length and init
lemmas. The proofs are identical up to the step function's name; a single lemma
quantified over the step function would serve all three. The later instance of each
pair is counted as the copy (`PolyTimeBlockTests` predates the split that produced
`PolyTimeBlockMajority`; within `Tests` the OR loop predates the XOR loop).

| Copy | Original | Overlap (renamed / exact) | Lines |
|---|---|---|---:|
| `Majority::length_majStep_iterate` | `Tests::length_xorStep_iterate` | 100% / 39% | 15 |
| `Majority::majStep_orbit_done` | `Tests::anyStep_orbit_done` | 100% / 49% | 16 |
| `Majority::length_majStep_le` | `Tests::length_xorStep_le` | 72% / 63% | 46 |
| `Majority::polyTimeComputable_majInit` | `Tests::polyTimeComputable_anyInit` | 53% / 38% (reverse direction 83%) | 8 |
| `Tests::xorStep_orbit_done` | `Tests::anyStep_orbit_done` | 53% / 27% | 21 |
| `Tests::xorLoop_output` | `Tests::anyLoop_output` | 51% / 19% (reverse 59%) | 30 |

All six members are `private`. Per-file totals:

- **`PolyTimeBlockMajority`: 4 of 14 declarations (28.6%, 85 lines). This is above the
  one-fifth threshold** (`workflow.md` §4), so a `backlog.md` §1 human-review item is
  opened.
- **`PolyTimeBlockTests`: 2 of 25 declarations (8.0%).**

**Class B: mirror pairs (dual statements; conventional, not counted).** These are
dual statements whose proofs coincide under the swap, the usual Lean
`_left`/`_right` pattern:

- `PolyTimeBlockLoop`: `polyTimeComputable_take1`/`_tail` and
  `polyTimeComputable_sliceTakeAt`/`_sliceDropAt` (100% renamed).
- `EmitIterBody`: `embed_ofWords_left`/`_right` (100% renamed).
- `PolyTimeBlockLoop::length_pairSndD_le` against
  `PolyTimePairing::length_pairFstD_le` (53% renamed, only 19 shingles — the Snd/Fst
  dual).

**Borderline (auditor to judge).**

- `PolyTimeBlockLoop::length_xorPairStep_le` against `length_sliceDropAt_le` in the
  same file: 87% renamed, 0% exact. They have the same proof shape over different step
  functions.
- `Majority::majStep` against `polyTimeComputable_majStep`: 55–63%. This is a
  definition overlapping its own poly-time proof, which restates its case structure;
  it is not believed to be duplication.

**Class C: copies of pre-existing repository material: none.** Matched against
everything outside the six files, the largest overlap is the 19-shingle Snd/Fst dual
above (53%). The rest:

| Surface declaration | Closest outside match | Overlap |
|---|---|---|
| `polyTimeComputable_or` | `PolyTimePairing::polyTimeComputable_and` (a dual) | 44% exact |
| `EmitIterEmbed::embedCfg` | `Oracle::Cfg.embedOracle` (a design parallel) | 42% renamed |
| `mem_P_of_blockMajority` | `PolyTimeModel::polyTimeModel_closedUnderMajority` (its consumer) | 25% |

None of the §12 material (`Build/Embed`, `Build/Seam`, `Build/Catalog`) or the loop
library (`Build/Loop`, `Build/Primitives`) appears among the matches.

## Design-level parallel (not mechanical; recorded in the ledger watch items)

`EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer
(`padAction`, `embedCfg`, `embed_step`, `embed_run`, `SafeRun`: 18 public
declarations, no private ones). It was written against `main`, which lacks the §12
`Build/Embed.lean` (attached to the bundle for comparison). The two layers are
independently written, and the screen finds no copies between them. Consolidating them
into one embedding API is on the **12.2c docket** (user decision, 2026-10-10).
