# 147-r3a-cleanup-gate

The first Codex audit for draft PR #336 (gate 147): chapters 3–4 closeout R3a, the zero-exposure slice of wave R3. It retires SK-1 and RC-4's buffer half by citation, deletes dead privates (CC7-1, C1E-1, the MIG-8 chain), and makes PL-1's `a3n_poly_linear` a citation (net −303 lines, no API).
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate147-r3a-cleanup-bundle.md` | the bundle to attach: 22 sections (one per file, in `BUNDLE-FILES.txt` order), 3619287 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `68eb27e741505a5e2dab4155ba202d4f69a804f93cf426b97207d39a5bac26ae`
- **Built by** `mkbundle-mixed.py`: the Lean files from `5da18960590c223ce384470e7d0d8870641f881c`, everything else from the
  campaign commit `2546c3e75a79e4bedefe2bb975306e8ba4fe53ac`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `22 segments, 0 problems`.
- **Findings:** the auditor delivers `gate147-r3a-cleanup-findings.md` as an attachment in chat; committed as `campaign/gates/147/findings-cleanup.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
