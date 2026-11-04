# External audit pack, round 3: four space facts out of `Machines/ARMWidth` (PR #181, an API gate)

**Rounds 1–2** (`pack.md`, `pack-r2.md`; findings `findings.md`, `findings-r2.md`; resolutions
`resolutions.md`): round 1 OPEN 0/1/1, round 2 **OPEN, 0 blockers, 1 major, 0 minors.** Round 2's
major: LS-1 was still not retired. Two inner steps derived the logarithm's form of
`logSpace m ≤ m + 1`, in `ImplicitPoly` and in `Logspace/PreimageHost`. Round 2's search had
classified both as different facts.

**The PR now:** #181 on `lean/logspace-move`, head `b8add1ac5bb0579d5a041e1a272787db7627c763`. It
holds rounds 1–2's commits, the fix commit `8d41671c` (`evidence/round3/patches/0003-…`) and a
merge of the campaign's later records commits, which changes no Lean. Against the campaign, #181
changes eight files: round 2's six, `SpaceComplexity/ImplicitPoly` and
`SpaceComplexity/Logspace/PreimageHost`.

## What changed since round 2 (verify)

| File · declaration | Change |
|---|---|
| `ImplicitPoly` · `Complexity.ImplicitlyLogspaceComputable.computesInSpace` | `have hWle : W ≤ F + 2 := by have := Nat.log_le_self 2 (F + 1); omega` becomes `have := Complexity.logSpace_le_succ (F + 1); rw [Complexity.logSpace_eq] at this; omega` (`W` is `Nat.log 2 (F + 1) + 1`, by `set … with hWdef`) |
| `Logspace/PreimageHost` · `Complexity.mem_LOGSPACE_preimage` | the inner `.trans (by have := Nat.log_le_self 2 ((f x).length + 1); omega)` becomes the same three steps at `(f x).length + 1` |

`ImplicitPoly` is Hydroxyi's: a register-machine program file, edited under the standing exception
for mechanical deduplication edits (FYI). `PreimageHost` is the campaign's. Freeze
(`evidence/round3/freeze/`): no declaration added or removed, no statement changed; only the two
named bodies.

## Brief for the auditor

1. **Is LS-1 retired now?** Are the two re-points correct? Is the classification right? It is
   `evidence/round3/ls1-search/classification.md`, over `ls1-search-raw.txt`: every use of
   `Nat.log_le_self`, every statement of a `logSpace` bound by a successor, and every citation of
   `logSpace_le_succ`, each classified. Its claim: the fact is proved once, in `Basic`, and cited at
   eight sites. The other `Nat.log_le_self` uses cite Mathlib's `Nat.log b n ≤ n` for other ends:
   `Lupanov` 213 and 269, `NTimeDiagonalizer` 5164, `BiasedCoinHalting` 445. Is any of them, or
   any other site, a copy of the fact in another guise?
2. **The ledger's LS-1 entry** (`campaign/duplication-ledger.md`), corrected twice: is it accurate?
3. **The screen, round 3** (`evidence/round3/screen/`): 17 files, round 2's 15 and the two above.
   Base `711f5444` (a `git archive` export), head `b8add1ac`: 124 → 124 declarations, 23 → 23
   pairs, 5,119 → 5,087 characters, no pair new and none gone. Is that right?
4. **Unchanged since round 2:** the six files of rounds 1–2. Confirm that round 3 touches none of
   them.

## Repository-side attestations (verify or challenge)

- **Elaboration** (`evidence/round3/elab/`): `ImplicitPoly` and `Logspace/PreimageHost` at the
  round-3 commit, against `oleans-lsm2` (the round-2 head's fresh snapshot; their imports are
  unchanged): 0 diagnostics each.
- **Replay:** `replay-lsm3.sh` (`evidence/round3/merged-tree/`), the eight files' downstream
  closure, 137 modules (the same closure: both new files were already in it). It builds fresh
  `.olean`s from `oleans-leqc3`, pinning the eight blobs. Precheck passed; **not yet run.**
  `replay-lsm2` (round 2's head) passed, 137 of 137, but no longer certifies the PR.
- **Overlap with #182** (gate 90): the user ruled that #181 merges first; #182 then takes one
  merged-tree replay of its closure on top.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/89-space-facts-api/findings-r3.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `space-facts-api-r3-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
