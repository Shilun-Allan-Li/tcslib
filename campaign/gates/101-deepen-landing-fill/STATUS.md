# Gate 101 (#208, the deepening fill's landing)

- 2026-11-06: the delivery received (`c7b179da`), reviewed by a sub-agent (2 majors, minors), and
  swept at the have level (5 hits); the maintainer's landing edits `a46e04a9`, `eeceae9f`; #208 at
  `a074d9b7`; `replay-ldp2` passed (3 modules, 0 `sorry`); the seal, axioms, freeze, screen and lint
  in `evidence/`. Pack complete.
- 2026-11-06: staged (`outbox/gates/101-deepen-landing-fill-gate/`, exchange commit `2c07a826`):
  bundle `101-deepen-landing-fill-bundle.md`, 83 sections, SHA-256
  `0e67a7cdd8b5f1b98afe5f1748da812fef381b666605122858d7d138cdf8004a`; Lean from `a074d9b7`, records
  from `c4a5d6d2`. Findings file `deepen-landing-fill-findings.md`.
- 2026-11-06: **dispatched** (the user).
- 2026-11-06: #209 merged; the campaign merged into the branch (`ca0af1c085d3135e040b6a65671dee58625b3984`, no change to the PR's
  files). `replay-ldp3` passed (3 modules, 0 failed, 0 `sorry`), chained from `oleans-lnth`
  (`evidence/merged-tree-after-209/`): the replay of record for the merge.
- 2026-11-06: round 1 findings received: **HOLD 0/1/3/3** (F1, the value-to-width bound in three
  files). The user ruled: harvest in #208, all three.
- 2026-11-06: the repair `9db4f2ee` on #208 (F1 harvested: `Complexity.LogProg.length_bits_succ_le`
  in `Machines/Bin`, the three sites re-pointed; F2–F4), then the campaign merge `dd8a52c5`.
  BL-2 in the ledger; dispositions in `resolutions.md`. `replay-ldp4` (190 modules) running; freeze
  and lint done.
- 2026-11-06: round 2's screen exposed IL-1 (six re-derivations of `indicator_inputLenLang`,
  all predating #208); the user ruled: re-point all six in #208 (`6a289c50`), then the campaign
  merge `d01c56a4`. #208 now changes 11 files. `replay-ldp4` was stopped (superseded);
  `replay-ldp5` (190 modules, from `oleans-lnth`) running.
- 2026-11-06: `replay-ldp5` passed (190 modules, 0 failed). Round 2's screen then showed the
  simp-set members of IL-1 and its sibling reading (`indicator_inputBitLang`); the user ruled:
  re-point all five in #208 (`0140aee2`), then the campaign merge `36ed2deb`. #208 changes 13
  files. `replay-ldp6` (190 modules, from `oleans-lnth`) running; the freeze and lint redone.
