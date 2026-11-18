# Gate 46 · resolutions, round 1 · CLEAR → docs-only landing edit LE-g46b

Codex's verdict is **CLEAR overall: #376 CLEAR, #377 CLEAR**: 0 blockers, 0 majors, 2 minors (G46-01, G46-02, #377)
and 1 note (G46-03, #377, known).
- **Findings:** `findings-r1.md` (filed by the maintainer, records `6f3c8c33`).
- **Audited:** #376 at `04ba2446f541c39dd02aefaa97a9eb31dbbda748`; #377 at `7563734a8badba842223e0687c719b3b4692e9d2`
  (stacked on `04ba2446`); exchange pin `8cfb07b12373974d324fb99f47fc2e035dce6aef`; campaign-records pin
  `1404eff9d9d9f55f7e4687a87395dec70dbb791e`.
- **Ruling (Seyoon, 2026-11-18), decision log "Gate 46 dispositions":** G46-01 and G46-02 are fixed by a docs-only
  landing edit LE-g46b on #377; G46-03 is known, and its merge condition is met by the efficiency remediation plan. #376
  is clear to merge; #377 is clear to merge after LE-g46b's checks pass. #376 has since merged (`d6dee3d0`, records
  `f968f6b2`).

Codex's round-1 confirmations stand unchanged (statement fidelity of all 24 targets, O2's interval reader for every
`q ≥ 2`, the `2^70` constant, 140/140 anchors, the evidence and execution recounts, and the grades of G6B-F01–F12 and S1).
LE-g46b changes comments and docstrings only, so none of them is reopened.

| Finding | Grade | Resolution | Evidence and pointer |
|---|---|---|---|
| G46-01 | **minor** (#377) | **Fixed by LE-g46b**, commit `e8553378636dc896f36fc2a5ab23c8336dbfcecb` on `7563734a` (tree `129bbf9d…`), signed by the records key. The `WeakCircularSecure` docstring (`GSW/Circular.lean:101–106` at the head) now restricts the "`ε` near `1`" explanation to parameters under which decryption is correct. It says that an unbounded test can enumerate the key-generation seeds, take any seed whose public key is `pk`, and decrypt the challenge with that seed's secret, and that recovering the original `s` uniquely is unnecessary. It adds that the definition also admits parameters that do not decrypt correctly, to which the argument does not apply. The predicate and its reader are unchanged. | `le-g46b.md` §"G46-01"; `le-g46b.diff.txt` (`a9fb6193…`); `le-g46b-evidence.zip` (`54512ea8…`). |
| G46-02 | **minor** (#377) | **Fixed by LE-g46b** (same commit). In the `encodeCiphertext` docstring (`GSW/Asymptotic.lean:77–81`), the attribution [Pei16, Def 4.2.3, p024-b001] (decision-LWE) is removed. The encoding is marked "Glue: a local encoding choice, which the cited sources do not fix", and [Pei16, §5.4.3, p052-b001] is cited only for the base-two representation of the canonical residue in `{0, …, q − 1}`. The anchor was verified in `blueprint/src/references/peikert2016-lattice-survey.md` (block `p052-b001`, §5.4.3 "Gadgets"; DW-7 extension). The module's `## References` entry for [Pei16] now names §5.4.3 instead of Definition 4.2.3, which no other passage of the file cited. | `le-g46b.md` §"G46-02"; `le-g46b.diff.txt`; `le-g46b-evidence.zip`. |
| G46-03 | **note · known** (#377) | **Known; no change.** The A4 domination hypotheses (`ReductionEfficient`, `LeveledReductionEfficient`) do not prove machine reductions or honest-algorithm efficiency. This is the single rule-15 item retained by the gate ruling. Its merge condition, that #377 does not merge until the lattice-wide remediation plan exists, is **met** by `briefs/efficiency-gaps/audit-r1.md` §5 (remediation plan; job EF-R1 proves both predicates for every `F` after #377 merges) and `briefs/efficiency-gaps/rulings-r1.md` (Q2 A: #377 lands as audited; EF-R1). | `findings-r1.md`; `briefs/efficiency-gaps/audit-r1.md` §5.1 (EF-R1 row), §5.2; `rulings-r1.md` Q2, Q11. |

**Code identity.** LE-g46b is comments and docstrings only. The comment-stripped texts of `Circular.lean` and
`Asymptotic.lean` are byte-identical to `7563734a` (code characters 2417 = 2417 and 8533 = 8533). In each file 3
mutation controls are caught and 1 negative control stays equal.

**Checks at the new head `e8553378`** (detail in `le-g46b.md`):
- **Replay.** The 6 downstream modules (`Circular`, `Asymptotic`, `GSW`, `Homomorphic`, `AdvancedEncryption`, root) were
  rebuilt on a `cp -al` copy of `olean-replay-6b-stmt-g46` (→ `olean-replay-6b-stmt-g46b`). Results: 6/6 rc 0, 0
  `error:`/`error(`; the only warnings are `sorry`, and they map EXACTLY to the 24 targets; state **1456/1456 OK**;
  rebuilt oleans link count 1. Snapshot #10 and the LE-g46 tree rehash 0/0/0. The output map has 1487 entries
  (`e7bb03b4…`); against the LE-g46 tree only the 2 edited oleans change.
- **decls2** `7563734a` → head: 0 ADDED, 0 CHANGED, 0 REMOVED.
- **Lint:** `style_lint` 0 findings in the 12 series files; `campaign_style_lint --check8b` FAIL/WARN line set
  identical (92/103 over 540 files), only the 2 INFO line counts change.
- **#377 description** records LE-g46b and Gate 46 CLEAR; the REST read-back equals the text sent.

**Merge condition (recorded, not an audit item).** On #377's merge, `olean-replay-6b-stmt-g46b` is adoptable if the
merge's Lean paths equal tree `129bbf9d`. They do for a merge into the records tip `f968f6b2` (`le-g46b.md`, §"Commit
and push").

Per the ruling, #377 is clear to merge once LE-g46b's checks pass. They pass (above); dispatch and merging remain with
the user.
