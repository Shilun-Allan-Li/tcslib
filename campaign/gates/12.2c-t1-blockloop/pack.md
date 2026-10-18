# External audit pack — 12.2c tranche T1, item 7 (CH7-D1): the countdown block-loop layer

Campaign: Arora-Barak chapters 3-4. **12.2c** is the maintainer's refactor
window, run as three tranches (`AroraBarakChapters3-4Plan.md` §4e, "12.2c
placement"). Each tranche gets a PR the user merges and **its own audit
gate**.

This item discharges the human-acknowledged duplication debt **CH7-D1**
(`audits/duplication-ledger.md`; `backlog.md`; the ch7 fill gate's round 2,
finding R2-2). The OR, XOR-then-OR and majority countdown loops of the ch7
block stack each re-proved the same orbit, length and init lemmas. The ch7
owner (Aparna) approved the refactor and the new public names (via the user).

The change is PR #18 (`integrate/12.2c-t1-blockloop`): the Codex commit
`379a4efe` on base `b4be0717`, and the maintainer's records commit. **No new
mathematics, and every public statement is frozen.** The gate closes on zero
blockers and zero majors. The duplication rule (`audits/TEMPLATE.md`, failure
mode 5) is in force.

**What you audit.** The surface: the new generic layer, the instance map,
the frozen statements, and whether the duplication is genuinely gone.

## What changed (verify)

- **New public generic layer**, `Complexity.BlockLoop` (17 declarations in
  `PolyTimeBlockLoop.lean`):
  - the round `step` and the chunk `emit`;
  - their polynomial-time lemmas and the countdown initializer;
  - the done-absorption, length-envelope, orbit, past-exhaustion and
    single-emission lemmas;
  - two engines, `loop_output` and `polyTimeComputable_countdown`.

  Three OR-specific publics live in `PolyTimeBlockTests.lean`:
  `length_flag_le`, `any_range_succ_flag`, `polyTimeComputable_orLoop`.
- **The OR loop is deleted.** The plain OR block test is derived as the
  XOR-then-OR test with an all-`false` mask, through two new privates
  (`zipWith_xor_self`, `zipWith_xor_blockAt`).
- **Majority's headline** is one `countdown` call.
- **Privates** go from 45 to 18 (4 added, 31 deleted). Lines go from
  500 / 653 / 469 to 789 / 228 / 243.
- **Frozen surface.** All 26 base public statements are byte-identical.
  22 are identical in full, including all six public definitions and
  `blockAt`, which `Randomized/PolyTimeModel` unfolds by `simp`.
  - Four theorems are re-proved, changing only their proof-sketch
    paragraphs: `polyTimeComputable_xorD`, `_blockAnyTest`,
    `_blockXorAnyTest`, `_blockMajorityTest`.
  - Two private docstrings change: `majStep` gains a sentence and
    `majLoop_output` gets a new sketch.
  - Tests renames two section headers and adds one. These comment-only
    changes are not listed in the brief's ground rules; rule on them.

## Brief for the auditor

1. **Freeze.** From the attached base and after sources, confirm each claim
   under "Frozen surface" above.
2. **The generic layer.** Blind-restate each of the 20 new public
   declarations. Is each true as stated, minimal in its hypotheses, and
   reusable beyond these three loops? Is the namespace `Complexity.BlockLoop`
   and its naming sound?
3. **The instance map.** Every former family member must now be either
   deleted, with its call sites citing the generic lemma, or a genuine
   instance carrying only per-loop content (the OR flag, the XOR mask, the
   vote counters). Report any member that still re-proves a generic fact.
4. **The OR-via-XOR derivation.** Verify that the plain OR test equals the
   XOR-then-OR test at the all-`false` mask, for every input, malformed ones
   included. Check that the derivation preserves the frozen statements of
   `polyTimeComputable_blockAnyTest` and `mem_P_of_blockAny`.
5. **Duplication (failure mode 5).**

   | Screen | Before (pairs / characters) | After (pairs / characters) |
   |---|---|---|
   | Six files (the three plus `PClosure`, `EmitIterBody`, `EmitIterEmbed`) | 125 / 47,734 | 41 / 10,045 |
   | The three files alone | 102 / 41,608 | 18 / 3,919 |

   - Cross-file pairs fall from 64 to 2. The brief stated 65; the maintainer's
     count is 64. The two survivors are pre-existing pairs between `PClosure`
     and `Loop` (`union_mem_P` ← `polyTimeComputable_or`/`_not`), outside the
     family.
   - The CH7-D1 census goes to 0 in all three files: Tests 22/25 → 0/8,
     Majority 12/14 → 0/6, Loop 6/32 → 0/50.
   - One new in-file pair remains, the brief's recorded 59% pair
     `BlockLoop.polyTimeComputable_step` ← `polyTimeComputable_xorPairStep`.

   Two proofs are deliberately not written in their one-line form, which the
   brief measured as creating cross-file pairs at 50–78%. Confirm that the
   chosen forms are honest proofs, not obfuscation of a copy.

   Does CH7-D1 count as discharged? Is any remaining pair a copy?
6. **Downstream.** The replay covers 24 modules. Confirm from the logs that
   `Randomized/PolyTimeModel` and `PClosure` elaborate unchanged.
7. **Docstrings.** Report any docstring made false. Check the four new
   proof-sketch paragraphs and the new module-docstring entries.
8. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Integrity.** The zip's `SHA256SUMS` is OK (the zip itself is not
  attached). The C shim is excluded and unreferenced. The delivered sources
  are byte-identical to the integrated files and to the maintainer's pre-ship
  reference sources (`audits/evidence/ch34-t1/Item7Ref-*`, same blob ids).
* **Freeze** (`audits/logs/12.2c-t1-blockloop-freeze.log`).
* **Replay** (`audits/logs/12.2c-t1-blockloop-replay.log`): 24 downstream
  modules, 0 errors, 0 sorries (as at base).
* **Axioms** (`…-axioms-{base,after}.{lean.txt,log}`): the 26 base prints are
  byte-identical after, and the 20 new ones are within the standard triple.
  No `sorryAx`.
* **Lint** (`…-stylelint.log`): 0 FAIL.
* **Screens** (`…-screen-{before,after}.txt`). The screen script and all six
  screened sources are attached at both base and after.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/12.2c-t1-blockloop-findings.md`.
