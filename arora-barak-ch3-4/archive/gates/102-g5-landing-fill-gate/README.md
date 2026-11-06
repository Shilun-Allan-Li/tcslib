# 102-g5-landing-fill-gate

Gate 102: the fill gate of G5's landing, PR #211 (`Turing.FinTM.two_work_tapes_run`), at `f239dafd09f060ec87ca0992103ae8eb48bce31e`.
The pack is `campaign/gates/102-g5-landing-fill/pack.md`, the bundle's first section. Omitted from the bundle but on the records branch: the sweep's copy A/B logs and `evidence/axioms/TwoTapesAxioms.lean.txt` (the head's `TwoTapes.lean` followed by one `#print axioms` per declaration).

| File | What |
|---|---|
| `102-g5-landing-fill-bundle.md` | the bundle to attach: 89 sections (one per file, in `BUNDLE-FILES.txt` order), 2775139 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `a79385da1ad4331dcb6559207ddcfcb29e1ab4dced93f4734015eaf068f0582d`
- **Built by** `mkbundle-mixed.py`: the Lean files from `f239dafd09f060ec87ca0992103ae8eb48bce31e`, everything else from the
  campaign commit `f6954560434dbf5c4a7777f29f1c481cee151f92`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `89 segments, 0 problems`.
- **Findings:** the auditor delivers `g5-landing-fill-findings.md` as an attachment in chat; committed as `campaign/gates/102-g5-landing-fill/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
