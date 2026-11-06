# External audit pack: dedup ZP-1, `ZoneRebalance`'s inline state-independence steps (PR #212, a dedup gate)

## Why this PR

The dedup window (12.2c) opened on 2026-11-06 (the user). It retires the ledger's acknowledged
families one PR at a time. **ZP-1** (`campaign/duplication-ledger.md`): `Turing.zoneRowPre`
(`TuringMachine/Build/ZoneRebalance`) reads only the work tapes and work tape `0`'s head, so it is
invariant under a change of state. #197 published that as `zoneRowPre_congr` and
`zoneRowPre_mapState_iff` beside the definition. The same file still proved it inline twelve
times, by unfolding `zoneRowPre` with `funext_iff`, `Cfg.mapState_workTapes` and
`Cfg.mapState_workTapePos`. That was legal in the definition's home, so it is not a rule-10 issue,
but it is duplication. The ruling (2026-11-05) scheduled the re-points for this window.

**The PR:** #212 on `lean/dedup-zp1`, head `034e72e3` (full hash in the bundle header): the
change `df78600e` on the campaign at `b1a9969a`, then a records-only merge of the campaign. It
changes one file, `Build/ZoneRebalance`: 14 lines added, 30 removed.

## What changed (verify)

Each of the twelve private declarations now cites `Turing.zoneRowPre_mapState_iff` in place of
the unfolding (`evidence/landing/zp1.diff`):
- `zr_rightSeekBack_post`, `zr_rightSeekBack_ruler_pre`: `simpa only [..., zoneRowPre_mapState_iff]`
  (the first also loses a duplicate `Contract.ofSegment_pre` entry);
- `zr_rightRuler_pre`: the same `simp only` list ending in the lemma;
- `zr_rightPass_pre`, `zr_rightReturn_pre`, `zr_rightLeft_pre`, `zr_extend_pre`: the lemma
  appended to the existing `rw`, the trailing `simp only` gone;
- `zr_rightReturn_post`, `zr_rightReturn_bounds`, `zr_rightLeft_post`, `zr_rightLeft_fields`,
  `zr_extend_fields`: `rwa [zr_<part>_pre, zoneRowPre_mapState_iff]`.

No statement, definition, import or docstring changes. A search of the file for other
state-independence arguments (`zoneRowPre` with `mapState`/`bindState`, the pin lemmas,
`zr_scanShort_pre`, `zoneRowPre_rebalancePost`/`_extendPost`, the `Contract.seq_pre`
neighbourhoods) finds none; the file has no `funext_iff` left. RN-1's `Cfg.ext` blocks are
untouched (ZP-1's entry explains why they are a different kind).

## Brief for the auditor

1. **Completeness:** does any site in `ZoneRebalance`, or elsewhere in the library, still prove
   `zoneRowPre`'s state-independence instead of citing `zoneRowPre_congr` or
   `zoneRowPre_mapState_iff`?
2. **Scope:** does the change touch anything beyond those twelve proofs?

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`): 25 → 25 public, 852 → 852 private; only the twelve private
  bodies changed.
- **Screen** (`evidence/screen/`): the v3 screen on `ZoneRebalance` alone at base and head: base 618 declarations, 532 pairs,
  225,542 characters; head 618, 487 pairs, 219,771 characters: **46 pairs gone** (the re-pointed
  bodies and their near-copies) and **1 new**, `zr_rightPass_time` against the shortened
  `zr_rightRuler_pre` (62%): the body of `zr_rightPass_time` is unchanged, and the pair appears
  only because the re-pointed body is shorter.
- **Lint** (`evidence/lint/`): the campaign lint on `TuringMachine` 0 FAIL, 71 WARN over 92 files
  (as at the base); the policy linter's 26 findings, the same as at gate 99 (the size line moves).
- **Replay** (`evidence/merged-tree/`): `replay-lzp1` at `034e72e3`, the downstream closure of
  `ZoneRebalance` (5 modules), chained from the campaign's `oleans-lnth`: **5 modules, 0 failed**;
  static 0 mismatches; the one `sorry` is `TwoTapes`' target, which #211 closes.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/103-zp1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `zp1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
