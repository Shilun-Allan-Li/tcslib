# 132-runfrom-one-r3-gate

The third Codex audit for draft PR #296 (gate 132, dedup family RO-1) checks the
repair of round 2's G132-04 (Bidirectional `foldCfg_run` now cites `runFrom_one`,
in 69 citing owners), the corrected sweep dispositions and the census that closes the
blind spot behind it. The bundle includes the verbatim round 2 findings, the fresh
merged-tree replay, the base-against-head seal comparison, the paired controls and the
copy screen. Return the findings Markdown in chat.

| File | What |
|---|---|
| `132-runfrom-one-r3-bundle.md` | the bundle to attach: 95 sections (one per file, in `BUNDLE-FILES.txt` order), 26572963 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `016e66449ef3187baaa247a7660ad30ffaa98c30cbf3a988f7bf7c9632db6a08`
- **Built by** `mkbundle-mixed.py`: the Lean files from `befb73f97a63ce449fe1a9a1b7dfc3fdbda65969`, everything else from the
  campaign commit `00b522b9169e45ee27932201a2ac55f49982d6e4`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `95 segments, 0 problems`.
- **Findings:** the auditor delivers `gate132-runfrom-one-r3-findings.md` as an attachment in chat; committed as `campaign/gates/132-runfrom-one/findings-r3.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
