# F6 re-triaged after #161 and U2's fill (maintainer, 2026-10-26)

**The item:** `Complexity.space_universal` (`SpaceComplexity/Hierarchy.lean:150`), the code-first
space-universal machine `SU` on `pairEncode (bits s) (pairEncode α x)`, within `C · s` cells. Its
place in the B6 plan is "off the headline's path; last (no consumer)": `space_hierarchy` uses `U₀`
(`SelfUniversal`), not `SU`. Megafill D's review (T4, F9) asked for a re-triage once #161 merged.
U2's fill (#168, not yet merged) changes the picture again.

**Verdict: not briefable until a harvest of U2's machinery lands; keep it last.**

- **#161's API is in** (`rulerHostCfg_*`, `forwardLoopCfg_*`, `pairEncode_drop`), so that blocker
  is gone.
- **`SU`'s route is U2-E's** (`Turing.universalK`), with a second header and a space ledger in
  place of the time bound. The steps are the startup, a header-ruler scan, the ruler's rewind,
  the ruler host `exists_rulerHostTM` and the forwarding loop. U2's delivery proves each piece
  as a private lemma of `UniversalK`:
  - the scan: `uk_scanTM`, `uk_scan_run`, `uk_scan_ruler`. They are already stated for one
    header read from any input position `1 + p` with `z.drop p = pairEncode u v`, so two runs
    give `SU`'s two headers;
  - the seam into the loop: `uk_loopTM` with `uk_loop_run`, `_forward`, `_live`, `_converse` and
    **`uk_loop_space`**, the space ledger `SU` needs;
  - the header phase and the host's start: `uk_headerTM`, `uk_header_run`, `uk_embed_suffix`.

  Rule 11 forbids citing them from `Hierarchy`, and re-deriving them is a duplication finding.
  The megafill C ruling on Q-U2 already says to "publish it when `space_universal` is briefed (its
  second consumer)". The review of U2's fill lists the scan and the seam as promotion candidates
  (F7).
- **The one open design point: the startup's input.** `Turing.exists_selfStartupTMK` reads its
  code at the start of the native input, and here the code is the second header. Its endpoint is
  uniform in the suffix (`T`, `B` depend on `α` only), so it can run on a buffered copy of
  `pairEncode α []` through the virtual-input host `vhostSilentTM`. The copy costs `O(|α|)`
  cells, a per-code constant inside `C · s`. A copy of the whole suffix would cost `Θ(|x|)`
  cells and break the bound.
- **The import union** for `Hierarchy` (the 2026-10-15 ruling: F6 and H share it, with H after
  F6) and **a fresh import probe** of the sketch's names are pre-ship items, unchanged.

**Proposed sequence, when F6 is scheduled:**
1. #168 merges.
2. **A maintainer API PR, the U2 harvest** (the A+ pattern):
   - the generic header scan and the seam family, as public rows, with field-equation API where
     a definition is published;
   - home: `UniversalK`, or a new `Build/` module if `Hierarchy` should not import all of
     `UniversalK`;
   - `UniversalK` re-pointed in the same PR;
   - its gate and replay.
3. F6's brief (Codex). It composes the published rows: two scans, the startup on the buffered
   header, the rewind, the ruler host, and the space ledger from the published loop space lemma.

**Decisions, for when F6 is scheduled (none needed now):**
- harvest first (recommended) or a private re-derivation in `Hierarchy`, which is a duplication
  finding;
- the harvest's home;
- F6's queue: megafill D's second item after E-Q, or later.
