# Facade-completeness lint fix (2026-11-14)

Seyoon ruled on 2026-11-14 to fix the bug by a PR on our branch. The `dl-crh` delivery reviewer found it.

## The bug
In `scripts/campaign_style_lint.py`, `check_facade` is meant to exempt a grandchild module that its facade imports
through an intermediate facade. The exemption looked for `D/D.lean`, inside the child's directory, instead of the
sibling facade `D.lean`. So it never applied: every facade had to import all of its descendants directly.

## The fix
`check_facade` now walks the intermediate facades `D.lean` between the child and the checked facade. The child counts
as covered when one of them is imported. That intermediate facade's own check then requires the child. The patch is
`lint-facade-fix.patch`, branch `fix/pass-shelat-lint-facade`, commit `3faaf477640473ec5635b3f76389efa114d51c43`.

## Effect at records tip `8b27fd69`
| Tree | Before | After |
|---|---|---|
| `TCSlib/Cryptography` | 216 FAIL / 102 WARN | 92 FAIL / 102 WARN |
| `TCSlib/Cryptography` facade-completeness lines | 173 | 49 |
| `TCSlib/Complexity` | 44 FAIL / 339 WARN | 25 FAIL / 339 WARN |

Every line other than the facade lines is byte-identical, and the fix adds no FAIL. The remaining 49 Cryptography
lines are true omissions of direct children (for example `Games.lean` does not import `Games/BitCodec`).

## Consequences
- **New baseline:** later gates and reviews compare against the fixed lint, from 92 FAIL.
- **cca2-ett:** its 19 new facade FAILs are false positives under the fix.
- **Facade-import edits:** the edits made for the old lint (ext-nosrc, dl-crh LE-facade, hash-sign, lamport) are
  harmless and stay in place.
- **Arora–Barak:** the script is shared with that campaign. Its copy is not touched, and the fix reaches it only
  when our branch is merged up.
