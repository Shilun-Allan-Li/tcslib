# 153-stage1-promotions-gate

The first Codex audit for draft PR #349 (gate 153): chapters 3–4 closeout, stage 1, small promotions and citations. Four approved public promotions (an NTIME halting-time acceptance lemma, Oracle's relabelling with a bundled reader in OracleFinite, a tape-general scan lemma, `pairEncode_drop` moved to Encoding), and citations replacing private copies across 18 files; CK-1, G147-01 and RS-1 carried by ruling. Statements unchanged, net −5 lines.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate153-stage1-promotions-bundle.md` | the bundle to attach: 36 sections (one per file, in `BUNDLE-FILES.txt` order), 9486847 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `a06e2ba0c746e07604bf8699fd970ecb5591f58b1fe31c4cd3d7bf621647d61f`
- **Built by** `mkbundle-mixed.py`: the Lean files from `a1a7c6ec39b515c6babc347e300a21566516a3a8`, everything else from the
  campaign commit `10a3f089514d068488df14f457a3661c8ca965c9`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `36 segments, 0 problems`.
- **Findings:** the auditor delivers `gate153-stage1-promotions-findings.md` as an attachment in chat; committed as `campaign/gates/153-stage1-promotions/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
