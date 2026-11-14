# Gate 23 · resolutions, round 1 · CLOSED

Codex's verdict is **HOLD**, with 0 blockers, 1 major, 1 minor and 0 notes.
- **Findings:** `findings/gate23-cca2-ett-findings.md`, SHA-256 `1a1c8aa2aec049e5d3dc54a8b0ff10cbcd8b3f33f65645bbbd3f26addc46ea2b`.
- **Audited head:** `c1a3ba5623febf318a56a0f84be885f262e0f86e`.

| # | Severity | Disposition |
|---|---|---|
| G23-01 | major | **Explicitly dispositioned as debt.** Seyoon ruled on 2026-11-14 ("Debt now, fold in cleanup"). The issue is the private `length_le_length_encodeLog` (`\|h\| ≤ \|codec.encodeLog h\|`) in `EncryptThenTag/Machines.lean`, which duplicates the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`. Neither copy is public. The fold is recorded under **DL-40**: publish the lemma in `Games/Efficiency/Strings.lean`, next to `length_encodeLog_le`, and delete both private copies, in the coming cleanup job. #306 keeps it as it is. |
| G23-02 | minor | **Fixed** by **LE-gate23** `b422ab5f01c131c7519ae1ff3bcff885a1debcab` (tree `10e02c545b599461066718ab5935a5c7142eb215`). |

## LE-gate23 (`b422ab5f`)

The commit changes 4 doc-comment lines in 4 files, and nothing else.

**The edits**
- `Reduction.lean:82`: `dAbs q E hE b n s` → `dAbs E hE q b n s`.
- `Handler.lean:40`: `dHandler E hE q b` → `dHandler q E hE b`.
- `CPAHandler.lean:39`: `bHandler q hq b` → `bHandler q`.
- `CPAReduction.lean:118`: `bAbs ((o, L), j)` → `bAbs q n ((o, L), j)`. A sweep of all 26 doc spans that name these
  functions found this fourth case. The maintainer accepts it.

Each argument order was confirmed against the declaration and every use of it.

**Checks**
- All hunks lie inside doc comments. With comments blanked, the files are byte-identical.
- All 372 headers are byte-identical.
- No line is over 100 characters.
- 19/19 modules give rc 0 through root `TCSlib`, and the full head check (1211 modules) is OK. Only the 4 edited
  modules' oleans changed.
- The new lint gives 92/102 at the head, with identical lines.
- `dl-oleans-2` was restored to the base snapshot (`457ba704…`).
- Evidence: `landing-r1/gate23-r1-evidence.zip`, SHA-256 `95ae7e8f153e5fc83b6851971cd86edf54722353daf663f478ee507a7de4f71c`.
  The patch is in `landing-r1/`.

**Merge readiness**
- A trial merge with the records tip (after #308 and #309) is clean, since the files are disjoint.
- A build of that combined tree is running as part of the post-merge check.

## Disposition
G23-01 is dispositioned under the ruling (DL-40), and G23-02 is fixed. **PR [#306](https://github.com/Shilun-Allan-Li/tcslib/pull/306)
is marked ready at `b422ab5f`.**
