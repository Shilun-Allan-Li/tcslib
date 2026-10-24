# Check 7: the megafill C cover draft

Draft: `campaign/fills/megafill/drafts/megafill-C.DRAFT.md` at `6e8db28f` (143 lines), against
`megafill-B.md` and `megafill-A.md` (59 and 60 lines), addendum v2.5 Part 3, and the drafting
brief's §7.

## Element by element

| Requirement | Cover | Verdict |
|---|---|---|
| Queue order with a reason | 58–84: C1, B5a, U2, G4, with a paragraph per item | present; recommendation below (Q-M1) |
| Shared base; preflight, toolchain, clone, cache once | 15–56: ancestor check, SHA check, Part 1 once with its floors, one fetch for the 41-root union (119 modules), the store logged first, the shared logs kept and copied into every zip | present; stronger than A/B (expected counts, store, manifest result). The 41 roots re-derived by the addendum's own command over the four order lists equal the env record's and C1's roots (`out/union-roots.txt`); B5a's, U2's and G4's lists are subsets of C1's 119 |
| Per item: re-bootstrap; branch from the shared base | 86–107 | present (each list named, with its count) |
| Per-item budgets and checkpoint zips | 60–70 (table), 100–105, 139 | present; B5a's budget carries the open ⟨Q-M2⟩ (69–70) |
| Addendum v2.5 with megafill A's lessons | 10, 121–135 | present (shared logs in every zip, per-module memory, seal not run / no controls a failure, the input-rewind population rule with each item's status) |
| The agent: Codex | 13 | present |
| Items dropped when a prerequisite is missing | 27–30 | present, but under-specified (below, F10) |

## Problems

1. **The SHA-256 table lists the cover itself** (37: "this cover | ⟨…⟩"). A file cannot carry its
   own SHA-256; A and B take every hash from the dispatch message ("its SHA-256 must be the one the
   dispatch message gives"). The addendum's Part 3 item 1 ("against the cover brief's table")
   reads literally as the draft does, so the fix belongs in the cover: the item briefs' hashes in
   the table, the cover's own in the dispatch message (F8).
2. **Cross-item effects on C1 that the cover does not state** (F9):
   - Under **Q-B1 (A)** the harvest PR "re-points `NDCodeSimulator` in the same PR" (the report's
     recommendation): C1's owned file changes before issue. C1's blob check (`e2cdab7b…`) would
     then fail at the fill's first step, and its line numbers (79, 95, 96, 99), counts (2,325 lines;
     22 private), order list (gains the new module), screen population (should gain it: its
     privates are `NDCodeSimulator`'s former ones) and screen base all change.
   - **#156's head moved after drafting**: `0e5f210b` (2026-10-24 04:53 UTC, "gate 69's major")
     now also edits `CodeSimulator.lean` (B5a's owned file, a private proof at 4593), and
     `Build/StepBlock.lean`, `Build/WindowRun.lean`, `Build/OracleSim.lean`,
     `SpaceComplexity/Inclusions.lean`; no import changes. If #156 merges before issue, C1's screen
     base (StepBlock and CodeSimulator are in its population) and G4's (`Build/Seam` is in its
     population) change, and B5a's whole pre-ship must be re-run. C1's citations are unaffected.
   The briefs' generic "re-run the pre-ship at the issue commit" covers this only if the
   maintainer knows which records move; the cover's issue-time list should say so.
3. **"Removed from the queue at issue, and the queue renumbered"** (29–30) is safe (no item depends
   on another; dropping B5a or U2 changes no other item's base, order list or the 41-root union)
   but it is not one edit: the dropped item appears in the brief list (22–25), the SHA table, the
   queue table, "Why this order", the per-item lists (90–98), "How the items relate", the
   environment bullet (132–135) and C1's in-flight sentence (82–83, B5a). Say "the cover is
   re-issued without it, every mention removed and the banners renumbered" (F10).
4. **The issue-time list** (comment, 3–7) omits: the ⟨Q-M2⟩ text (69–70); moving each draft to
   `briefs/` without its comment and staging its inputs (each pre-ship README says how); the item
   banners (number, cover file name, budget wording without "(the cover's proposal)"); and G4's
   own issue-time items, two of which the drafting report does not list (out/08, F11).
5. Minor wording: "Never switch branches while a screen runs" (70) is safe but stronger than
   needed: `copy-text-screen-v3.py` reads every input file before it starts comparing (line 92 of
   the script), so a run on a separate worktree frees the clone at once. Relevant to Q-M2.

## Q-M1 (queue order): keep C1, B5a, U2, G4

- **C1 first**, more strongly than the draft argues: the review proves the target end to end
  under a 21-definition seal (`out/03-route-soundness.md`), about 300 lines. C1 finishes in its
  slot unless the environment fails, and makes two landed targets admission-free (both consumers'
  only admission source is the target: `out/04`). If the user supplies the review's proof as an
  input (decision D1), C1 needs about 2 hours, not 3.
- **B5a second, if Q-B1 is settled in the shared base**: the most valuable, the largest and the
  longest-budgeted item, while the session is young. If Q-B1 is (A) and the harvest PR has not
  merged, B5a drops and U2 becomes item 2.
- **U2 third**, its two checkpointed phases (a U2-U partial is useful), if Q-U1's API PR is in.
- **G4 last** with "the rest": an open-ended chain whose four earlier rounds each ended partial;
  any order that put it earlier would cap it at a fixed budget for no gain.
- Rejected alternative: U2 before B5a (likelier to complete, so more delivered if the session dies
  early). Megafills A and B both ran to the end, and B5a's long screen is better placed early.

## Q-M2 (B5a's 87-minute screen against its 5-hour budget)

Two runs take about 174 of B5a's 300 minutes. The before run hides behind the bootstrap and the
first proofs (it may run beside the one Lean process); the after run cannot, since it must see the
final file. Counted inside the budget, B5a would have about 3 hours of proof time for an item the
report sizes at 800–1,900 lines.

**Recommendation: the drafting agent's option**, made precise: B5a's budget counts up to the start
of its after run; B5a writes its last checkpoint zip before starting the after run (so a session
lost during the 87 minutes loses nothing), starts the after run at the latest when the budget ends,
writes `REPORT.md` while it runs, and the next item's branch is created only after the run has
ended and B5a's zip is written. This keeps "never return to an earlier item" literally true.

Alternative (more efficient, the user's call): run B5a's after screen on a separate worktree of
B5a's final commit (`git worktree add`), start U2 at once, and add the screen output to B5a's zip
when it ends: the only permitted return to an earlier item; U2's before screen waits for it (one
screen at a time). Raising the budget to 6 hours inclusive (the other option) still leaves only
about 4.5 hours of proof time and wastes the hour when B5a ends early.
