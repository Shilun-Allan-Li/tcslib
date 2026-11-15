# Gate 32 · resolutions, round 1 · CLOSED by disposition

Codex's verdict is **HOLD**: 0 blockers, 1 major, 0 minors, 0 notes.
- **Findings:** `findings/gate32-headd-promote-findings.md`, SHA-256 `fc8b1a58f45624952ae74aaa514a1d287b742abdfd3584aba27657e8d44b7937`. Codex's companion ZIP was not supplied; the Markdown is the record.
- **Audited head:** `c18afbe66101381eed1617801d942dcf691506ea`, records `34330972`, exchange `22df0b71`.

Everything else passed:
- pack integrity;
- the two-path diff;
- the placement in `BitLists`: it has Mathlib-only imports, and no import changes or cycle;
- the 23 headers, which are byte-identical;
- the proof and its documentation;
- name resolution;
- the seals and controls;
- the build and axiom evidence;
- lint;
- the #313 and #315 consumer checks.

| # | Severity | Disposition |
|---|---|---|
| G32-01 | major | **Ruling (Seyoon, 2026-11-15): extend DL-47 and close.** Codex found 16 more pre-existing occurrences of the headD/getD-of-`List.ofFn` fact that DL-47 did not list. One is an exact copy of the promoted statement, GGM `Run.lean:449` local `hbit`. Every relevant file has the same blob at the parent, the head and the pin, so none comes from #316. All 16 are now in DL-47, with locations and the cleanup plan Codex proposed: one generic getD reader derived from `headD_drop_ofFn`, then proof-only re-points, starting with the GGM copy. The `Garbling.lean` and `Yao.lean` copies wait for sc-garble and sc-yao. #316 is unchanged. Codex allowed this disposition as the alternative fix, so there is no round 2. |

**Gate 32 is CLOSED.** One merge condition remains: an integration rebuild of #316 on the tip with #314, combined
with #315 and #317, whichever of these merges second.

**After #316 merges:** #313 re-points `firstBit_of_pos` (LE-gate29b), and then Gate 29 round 2 runs.
