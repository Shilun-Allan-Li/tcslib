# W7: the integration PR into `main` (2026-11-17)

**Branch** `closeout/w7-integration` at `de95c67059eb90835b426809618b32cf706fb397`: one commit on
the campaign at `4542055414ba4a4b00aaceca692b16165c0216c4` (Lean `c91f4701`, the #363 merge).
`main` (`b986b862`) is an ancestor of the campaign (W4), so the PR merges without conflict and
the merged tree is the branch's tree.

**Shape (D5, Seyoon 2026-11-16; refined 2026-11-17).**
- `campaign/` and `devtools/` are left off `main`.
- `.claude/CLAUDE.md`, `AGENTS.md` and `machine-library-design.md` keep `main`'s text: their
  campaign notes link into `campaign/` (Seyoon, 2026-11-17: "leaving main as is").
- The rest reaches `main`: 217 Lean files under `TCSlib/` and `TCSlib.lean`, 76 blueprint files,
  and `scripts/lean_check_tree.sh` (`lean -j4`). In all, 295 files change against `main`.

**D6 (Seyoon, 2026-11-17).** `Diagonalization/Ladner.lean`'s `Authors: Codex` becomes
`Authors: Seyoon Ragavan`. This is the only Lean difference from the campaign.

**Build on the merged tree.** The branch's Lean equals the campaign's except for Ladner's header
comment. Ladner compiled at the branch head against `oleans-cc91f4` (exit 0, no output, pool slot
under the 2026-11-17 rule) produces an object byte-identical to the snapshot's (SHA-256
`46723e85…0a5f`). No downstream object can change, so `oleans-cc91f4` (898 objects, adopted
after #363 by a 129-module replay) is the build of `main` after the merge.
`w7/ladner-compile.log` is the (empty) compile output.
