# 168-ram-run-r2-gate

Round 2 of the Codex audit for draft PR #383 (gate 168) on the RAM work branch: tier 2 job E, the stage-2 simulation. Round 1 was HOLD (0/1/2). G168-01 is factored (three shared helpers in `Sim/RunStep`); G168-02 is answered by a final-head admission walk (13 roots reach exactly `exists_phase` and `exists_verdictPhase`); G168-03 by bundling all 19 citation homes and screening them (24 new pairs, all classified). Replay 286/286, seals and controls pass.
Read `pack-r2.md` (after the standards and round 1's `findings.md`). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate168-ram-run-r2-bundle.md` | the bundle to attach: 64 sections (one per file, in `BUNDLE-FILES.txt` order), 12054024 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `c64551e294345a8e502e7fb28049c73b35f087b6629f1eab50a7f4dc313810eb`
- **Built by** `mkbundle-mixed.py`: the Lean files from `230c39f53b31396fc8392132033839b6f64075fc`, everything else from the
  campaign commit `114d35a15fcc82cd58beefe112c440045808daa9`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `64 segments, 0 problems`.
- **Findings:** the auditor delivers `gate168-ram-run-r2-findings.md` as an attachment in chat; committed as `campaign/gates/168-ram-run/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
