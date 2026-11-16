# 149-r4-2-cleancall-gate

The first Codex audit for draft PR #342 (gate 149): chapters 3–4 closeout, wave R4, item R4-2. SAT and Cook–Levin hardness each carried a private copy of the same clean subroutine-call layer: a stop adapter, the clean-module contract, the bridge bound, install/emit modules, the first-halt cut and the guard join. One copy moves into the new public module `ClassNP/CleanCall` (eight declarations, approved with R4-2), and both files cite it. Net +66 lines, over the +50 stop rule; Seyoon accepted the overshoot. There are no public statement changes.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate149-r4-2-cleancall-bundle.md` | the bundle to attach: 33 sections (one per file, in `BUNDLE-FILES.txt` order), 3739366 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `bf08735f7c4505476130f32c6639c9ee0d9541b5d5aeb16cf2051e35d7fcbe67`
- **Built by** `mkbundle-mixed.py`: the Lean files from `a12da4d3fb38a849a7c5e8b7cdfd09e2cb30dfb7`, everything else from the
  campaign commit `ef26e3a9ec2cdf0df37e9203e980bf0344f4646f`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `33 segments, 0 problems`.
- **Findings:** the auditor delivers `gate149-r4-2-cleancall-findings.md` as an attachment in chat; committed as `campaign/gates/149/findings-cleancall.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
