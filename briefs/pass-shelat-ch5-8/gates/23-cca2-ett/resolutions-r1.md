# Gate 23 · resolutions, round 1 · IN PROGRESS

Codex's verdict is **HOLD**, with 0 blockers, 1 major, 1 minor and 0 notes.
- **Findings:** `findings/gate23-cca2-ett-findings.md`, SHA-256 `1a1c8aa2aec049e5d3dc54a8b0ff10cbcd8b3f33f65645bbbd3f26addc46ea2b`.
- **Audited head:** `c1a3ba5623febf318a56a0f84be885f262e0f86e`.

| # | Severity | Disposition |
|---|---|---|
| G23-01 | major | **Explicitly dispositioned as debt.** Seyoon ruled on 2026-11-14 ("Debt now, fold in cleanup"). The issue is the private `length_le_length_encodeLog` (`\|h\| ≤ \|codec.encodeLog h\|`) in `EncryptThenTag/Machines.lean`, which duplicates the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`. Neither copy is public. The fold is recorded under **DL-40**: publish the lemma in `Games/Efficiency/Strings.lean`, next to `length_encodeLog_le`, and delete both private copies, in the coming cleanup job. #306 keeps it as it is. |
| G23-02 | minor | **Being fixed by LE-gate23.** Three docstring argument lists (`dAbs_eq`, and the `dHandler` and `bHandler` module lists) are corrected. The change is docstrings only and is rebuilt. |
