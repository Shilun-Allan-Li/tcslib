# FRZ-1: the past declaration freezes re-checked with qualified names (maintainer, 2026-10-25)

**The item** (`campaign/backlog.md`, FRZ-1, from gate 78's minor 2): `declfreeze.py` up to v3
keyed declarations by their short name. Where two declarations in one file share a short name in
different namespaces, v3 kept only the last of them on each side of a freeze. A change to an
earlier namesake (a statement or body change, an addition or a removal) was therefore not reported.
v4 keys by the qualified name.

**Result: no change was missed in any campaign freeze.** Across every Lean file the campaign
changed, only two landings ever changed a declaration that v3 could not see. Neither was gated with
v3:
- **`8f26ddd2d645eb27bbddab51a86334bf74ac802c`** (2026-09-30, `Merge pull request #2 from
  Shilun-Allan-Li/final-project-cleanup`, Jason Dong). It removed 12 declarations from
  `CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound.lean`, 6 of them hidden from v3
  (when the file was split into its `FuncDisjointnessLowerBound/` modules). This is not campaign
  work, and no campaign freeze covers it.
- **`dc8d040901df67af3f575996790b7dfb0313d5b3`** (2026-10-15, #100, `lean/diagonal-p1`, Diagonal's
  parameterization). It added `DiagSimulator.diagLang_not_mem_DTIME`, `DiagSimulator.time_hierarchy`
  and `DiagSimulator.time_hierarchy_of_pos`, namesakes of three existing theorems, which v3 would
  not have listed as added. Its freeze was not `declfreeze.py`. It was the item's own
  qualified-name script (`campaign/items/diagonal-p1/scripts/freeze.py`), and its log
  (`campaign/items/diagonal-p1/logs/freeze.log`, "New declarations (14)") lists all three.

**The four open PRs gated before v4** (#164, #165, #166 and #167's base/head pairs): no changed
declaration has a colliding short name (`out/open-prs.txt`). #167's own freeze is already v4.

## Method (`scripts/`, run against the campaign tip `d90a89035846b902d2bdeb6c90584ed24d95347f`)

1. **The census** (`census.py` → `out/census-at-tip.txt`). It runs v3's and v4's declaration
   splitter (`df3lib.py`, `df4lib.py`: `declfreeze_v3.py` and `declfreeze_v4.py` cut before their
   report code) over every `TCSlib` file. **13 files have colliding short names**, among them
   `Build/Contract/Basic` (`trans` three times; `live`, `mono`, `segment` and `zero` twice) and
   Hydroxyi's `Diagonal`. The two splitters cut every file into the same chunks; only the keys
   differ.
2. **The history walk** (`history.py` → `out/history-walk.txt`). It covers the 815 Lean files
   changed on the campaign branch's first-parent chain since 2026-09-01
   (`out/campaign-changed-files.txt`), every consecutive pair of each file's versions on that
   chain (each PR's landing is one step). It flags each changed declaration whose short name
   collides on either side. Each is marked **visible to v3** when it is the last of its short name on
   every side where it exists (so v3 compared exactly it), and **invisible** otherwise. It walks the
   whole chain, not only the files that collide today, so collisions since removed are covered too.
   The walk prints one `done` line per file (815) and two flagged transitions (above).
3. **The open PRs** (`pair.py` → `out/open-prs.txt`): the same check on each open PR's head
   against its merge-base with its base branch.

To reproduce, from a clone at the tip:
`python3 -I campaign/items/frz1/scripts/history.py <tip> <file>` per file of
`out/campaign-changed-files.txt`; and `python3 -I campaign/items/frz1/scripts/census.py TCSlib`.
