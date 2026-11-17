# 154-stage2-fills-gate

The first Codex audit for draft PR #350 (gate 154): chapters 3–4 closeout, stage 2, three delegated fills. Four approved public lemmas (an NDTM first-halt row, the action tape-half lemma, a general seam space bound, and the window predicate as an equation), with UniversalK's input rewind, one-step window proofs and CodeSimulator's renamed configurations re-pointed to public rows, and the universal capture moved onto Build/Embed. One definition body changes (`universalCaptureTM`); statements unchanged; net −177 lines.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate154-stage2-fills-bundle.md` | the bundle to attach: 47 sections (one per file, in `BUNDLE-FILES.txt` order), 10568843 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `82cb0635112fb7a23932f70fa32d3bc5c3480aeec7d4c656d66cfc9999a0227a`
- **Built by** `mkbundle-mixed.py`: the Lean files (changed owners and citation homes) from `f2d1ead707d9ba12779dd0b377daba708bac8915`, everything else from the
  campaign commit `83a16a6d12df68570edc470f3475a1526f03e4d5`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `47 segments, 0 problems`.
- **Findings:** the auditor delivers `gate154-stage2-fills-findings.md` as an attachment in chat; committed as `campaign/gates/154-stage2-fills/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
