# 155-ch24-compat-gate

The first Codex audit for draft PR #354 (gate 155): chapters 3–4 closeout, compatibility with `cryptography/pass-shelat-ch2-4` ahead of that branch's merge into main. ch2-4's versions of the rule-10 readers both campaigns published are adopted (their exact text, our own readers moved clear), and ch2-4's `exists_pairMapSnd_computesInTime` is ported onto `pairMapSndTM` with its statement unchanged. ch2-4's future Lean conflicts drop from 11 to 4. Ten public declarations added, two readers' text changed; net +80 lines.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate155-ch24-compat-bundle.md` | the bundle to attach: 27 sections (one per file, in `BUNDLE-FILES.txt` order), 7780993 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `a98076dae49e10240ec57fce652b3034a80f1a6fecd24dbbdb125eb1f484ee45`
- **Built by** `mkbundle-mixed.py`: the Lean files from `718dddc66d5d4dad7ea25f299a01931be6c42658`, everything else from the
  campaign commit `25001750f960cd7afeca4bbcf219bb1ae6057d5f`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `27 segments, 0 problems`.
- **Findings:** the auditor delivers `gate155-ch24-compat-findings.md` as an attachment in chat; committed as `campaign/gates/155-ch24-compat/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
