# 150-k3-padding-gate

The first Codex audit for draft PR #343 (gate 150): chapters 3–4 closeout, wave R4, SG1 kind 3. SAT and Cook–Levin hardness drop their private padding copies and pad through the public `Build/EmitIterEmbed` layer. To let the rewritten proofs read the padded and forwarded configurations without unfolding them, `Build/EmitIterEmbed` and `Build/Wrappers` publish field equations for `embedCfg` and `emitCfg` (approved by Seyoon). Net +6 lines, no other public statement changes.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate150-k3-padding-bundle.md` | the bundle to attach: 28 sections (one per file, in `BUNDLE-FILES.txt` order), 6950928 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `f982e715353c1133e01a586c80365cbf5234066f257659708b652984a3e88b6c`
- **Built by** `mkbundle-mixed.py`: the Lean files from `0b12a1b30ad0fb8b800b67beb806766e6f266b86`, everything else from the
  campaign commit `37458a90580eaf73e9c0f32079c61374b0d7ee05`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `28 segments, 0 problems`.
- **Findings:** the auditor delivers `gate150-k3-padding-findings.md` as an attachment in chat; committed as `campaign/gates/150-k3-padding/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
