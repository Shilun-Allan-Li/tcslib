C1, the seam layout: **`Turing.exists_seamLayoutTM` is proved** (`Build/SeamLayout.lean`). One machine
redistributes a captured serialization `s = pairEncode a ((1^q 0) ++ v)` onto the step block's
table tape (`v`) and summary tape (the unary word from cell `2`), clears the source, returns every
head to `0` and frames everything else, silently, at one time `T ≤ 18·(|s| + 1)` fixed before the
configuration, and not before. The step-block startups cite it (U2-S's, R's, B5a's H1). The fill
delivery `fill-c1-seamlayout.zip` (SHA-256 `18442008…3083a`) is complete (1/1).

**Commits** (on the campaign branch):
- `bfe3e023`: the worker's six commits (`d6dd89ab..09773a66`, on `1c06ea94`) squashed into one,
  with the worker's authorship; the file is byte-identical to the delivered one. The squash drops
  campaign-labelled subjects and a private session trailer.
- `7cd01f84`, the maintainer's, docstrings only: the module's main results and the
  `TuringMachine` facade's line say "proved".
- `126127b8`: the campaign branch merged in after #139 and #143 (no conflict; this PR's files
  byte-unchanged).

**What it adds:** 35 private `sl_` declarations (the two framed leaves, the pair skip and the
unary split; the word identities through `TuringMachine/BufferWords`; the eight hosted phases) and
the `BufferWords` import. The route is the target docstring's: eight phases on one
`Turing.phaseHostTM`, seven dispatches, `C = 18`, `T = 2n − r + 4h + 5q + 2|v| + 23`.

**The user's rulings (2026-10-22):**
- **The route's one deviation is accepted** (the review's F1). Phase 8 runs through
  `phaseHostTM_run` with a self-redirect on the clear row's `done`, not through the agreement
  transport the brief prescribed: that transport's premise is a table fact about `phaseHostTM` that
  no lemma publishes. The two hosts' transition tables are equal, so the machine, its time and `C`
  are as briefed. A published last-phase lemma for the phase host follows in a small API PR.
- **Proof sketches follow up** (F3): 14 private proofs over 20 lines have no "Proof sketch"; a
  docstring-only PR adds them after this one merges.

**Review** (sub-agent; `campaign/fills/c1/reviews/seamlayout-1/REVIEW.md`; "complete; land"):

| Check | Result |
|---|---|
| Integrity | `SHA256SUMS` 33/33; the bundle (sole prerequisite the base), the six commits and the patch series agree with the delivered file |
| Scope and freeze | regions (a0), (a), (b) only; the statement, its docstring and the module header byte-identical; one import |
| Elaboration | 0 errors, 0 warnings at the base and at the tip |
| Axioms | the target on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; 36 prints equal to the worker's |
| Rule 10 | two seals (15 definitions; 19 with `Action.apply` erased from the simp set), controls biting at both ends; every rewrite argument inspected |
| Probes | the brief's 45 checks and the worker's 110, 0 errors |
| Edge cases | the delivered machine run on the gate's eight instances; the auditor's times 37, 34, 66, 49 reproduced |
| v3 screen | 867 → 897 declarations; 31 new pairs, all in-file, maximum 89%; no cross-file pair |
| Lint | 0 FAIL; the one new WARN is the file's size |
| Sweep | 94 modules, 0 errors; sorry warnings 35 → 34, every other unchanged by name |

The maintainer re-elaborated the landed head against `oleans-lg4c2` (0 errors, 0 warnings) and
re-linted (`TuringMachine/Build` 0 FAIL, 31 WARN over 39 files).

**Replay:** `replay-lsl.sh`, the merged tree at `7cd01f84` (every file changed since #132's merge,
14 modules: `Build/SeamLayout` and the campaign's merges of #133, #134, #136-#138 and #140, the
facade last), chained from `oleans-l132b`. **Passed (user, 2026-10-22):** 14 of 14, 0 failed,
static-equal (8). #139 and #143, merged since, meet this PR's closure (`Build/SeamLayout`, the
facade) only at the facade.

**Gate:** gate 59 (`campaign/gates/59-c1-seamlayout-fill/`), a fill gate. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
