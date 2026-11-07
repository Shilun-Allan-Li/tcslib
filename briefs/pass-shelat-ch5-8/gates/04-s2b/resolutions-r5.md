# Gate 04 (S2b, #195): round 5 resolutions

**CLOSED: 0 blockers, 0 majors, 3 minors returned.** The pack's closing threshold is
0 blockers and 0 majors. The audited Lean head remains **`9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`**; no Lean file was changed
for these resolutions. #195 is clear for the user to merge at that head.

- Findings: [gate04-s2b-r5-findings.md](findings/gate04-s2b-r5-findings.md), filed verbatim;
  SHA-256 **`40507f3a20d770deea84c9136d48e1fb8167f19bff40b3438a7bd509238588fe`**, also recorded in the adjacent `.sha256` file.
- Intake, 2026-11-06 PST: the user announced a local inbox delivery. The file was untracked in
  the shared exchange checkout, so there is no delivery commit to cite. Its bytes, rather than
  the checkout's HEAD, identify the delivery.
- Pinned pack records: `c39f0e118f1c0f89325cbc828401a5c024bb36d1`; staged bundle: 66 sections,
  SHA-256 `d5b1fc8ff952b05ee4086494970c537d250f42091af6979989c8bc63e21e550b`.
- GitHub was checked live: #195 is open and its head equals the audited head.

| Finding | Resolution |
|---|---|
| R5-01, minor | **Confirmed; coverage claims qualified and scanner continuation bug repaired.** The collector enumerates stored constants, not every anonymous command. The scanner is a TCSlib-name text scan, not Lean's syntax parser. The old scanner's comment-only continuation false negative was reproduced; the repair skips blank/comment-only continuation lines, passes 12 focused regression cases (including `delta`, nested comments, line numbers, dedent/`at` boundaries, `nth_rw` and `nth_rewrite`), and rescans the same head/candidate inputs at 0/0/0. **The anonymous-command collector gap is not declared fixed.** For this head, the independent auditor reports a broader import-closure seal of all 26 targets (6,322 file/name pairs), all passing. Future whole-file reviews must cover anonymous commands with a conservative foreign-definition list or command-aware collection and a failing control. See [the erratum](evidence-r5-review/ERRATUM.md) and [tooling follow-ups](../../maintainer/tooling-followups.md). |
| R5-02, minor | **Fixed in records.** The PR delta, implementation delta, seal set and replay scope are named separately. The candidate table now counts post-notation active rows: 260 active pairs, one further globally irreducible pair, seven omitted `PolyExpr.eval` rows, zero `glNeed` rows. The intermediate statement comparison is labelled with its actual revision pair; a direct round-4-to-head comparison is supplied. The worker report explicitly counts all four deferred efficiency proofs. Original frozen evidence remains available at the pack's pinned records commit. |
| R5-03, minor | **Confirmed; scheduled in clean-up part 2, item L.** The two equation statements survive once each, but their formula docstrings are incomplete. A concrete [docstring-only patch](evidence-r5-review/interaction-docstrings.diff) supplies every argument of `Protocol.transcriptWith_eq` and `Protocol.outV_eq`. Its comment-stripped source agrees with the audited source. This is a prepared follow-up, not a landed Lean change; it goes through the clean-up PR. The audited head remains unchanged. |

Round 4 follow-through:

- **R4-01: fixed.** The classifier uses elaborated signatures; the empty seed derives empty
  ledgers. The auditor verified all twelve named changed declarations and their equation-based
  repairs.
- **R4-02: not fully resolved as a general tooling claim.** The repaired scanner cases and
  stored-constant traversal are verified; anonymous-command collection remains a recorded
  follow-up. The broader independent seal supplies the current gate's coverage. This
  supersedes any reading of `resolutions-r4.md` as claiming the general gap was closed.
- **F02: fixed.** The auditor confirms the published equations, bridge re-proofs and controls.

The auditor's independent Lean results are reported evidence: the maintainer did not repeat the
122-module head bootstrap or the 26-file conservative seal on this Mac. The maintainer did
reconstruct the frozen bundle, recompute file sets/candidate counts, regenerate the direct source
comparison, reproduce and repair the scanner false negative, and rerun the hardened text scan.
The local 62-module base bootstrap is separate evidence and is not substituted for the audit.

Four inherited explicit `Function.comp` uses in `MultiMessage.lean`/`MultiMessageLemmas.lean`
are outside the TCSlib-only source scan. They are explicitly queued in clean-up part 2, item J,
with [locations](evidence-r5-review/inherited-core-unfolds.tsv) and a
[proposed equation-lemma patch](evidence-r5-review/core-comp-equations.diff). That proof patch is
not applied or Lean-checked here. These are inherited policy debt, not four new PR reads or an
assertion that the TCSlib scan covers core definitions.

Next: the user merges #195; gate 08 still awaits its findings. Clean-up/efficiency issue and gates
03/06 follow their recorded prerequisites. S2's external fill brief follows gate 08 closure and
#227's merge (Q4 (B)).

**Clear to merge — #195 at `9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`; gate 04 round 5 meets its closing threshold.**
