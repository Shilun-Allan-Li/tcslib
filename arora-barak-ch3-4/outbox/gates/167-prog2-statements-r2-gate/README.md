# 167-prog2-statements-r2-gate

The Codex re-audit for (a5) PROG-2 (gate 167, round 2) on the RAM work branch: the revised statement mirror of Light with string input and output and coins, now with the compiler stated concretely (streams, a time-independent footprint, padding and probability transfers, and the corrected PolyTimeComputable corollary). Round 1 was HOLD (0/4/2); resolutions.md maps each finding to its repair. No Lean PR; the mirror elaborates with 0 errors.
Read pack-r2.md (after the standards), then findings.md and resolutions.md. Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate167-prog2-statements-r2-bundle.md` | the bundle to attach: 34 sections (one per file, in `BUNDLE-FILES.txt` order), 584355 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `24a9bc3bdee2eb10f8cd709ff67e1c3a437ab4fc1369b93aa1ffb723a2ad917f`
- **Built by** `mkbundle-mixed.py`: the Lean files from `090dbca236bfbb05005cb664a74716543abddc58`, everything else from the
  campaign commit `090dbca236bfbb05005cb664a74716543abddc58`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `34 segments, 0 problems`.
- **Export:** only the 34 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate167-prog2-statements-r2-findings.md` as an attachment in chat; committed as `campaign/gates/167-prog2-statements/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
