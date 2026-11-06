# Gate 104 (#213, the dedup window's CE-1)

- 2026-11-06: the change (a sub-agent's alias `32071598`, then the deletion `fdc0e425` following the
  disposition), #213 opened. `replay-lce1` passed (7 modules, 0 failed, 0 `sorry`); freeze, screen,
  lint in `evidence/`. Pack complete.
- 2026-11-06: staged (`outbox/gates/104-ce1-dedup-gate/`, exchange commit `64b4a9ec`): bundle
  `104-ce1-dedup-bundle.md`, 22 sections, SHA-256
  `a93def64915f6cd9c2c63b32998b7e0a2a359b6c698f75ea90ebf3b3a2a12b0d`; Lean from `fdc0e425`.
  Findings file `ce1-dedup-findings.md`. **Ready to dispatch.**
- 2026-11-06: **dispatched** (the user).
