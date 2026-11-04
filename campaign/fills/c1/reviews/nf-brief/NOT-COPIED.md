# Not copied from the review's scratch folder

- **`wt/`, the review's worktree.** It was detached at `c2887fb5` (#174's merge), with the
  `.lake/packages` link, and was removed at the end with `git worktree remove --force`. It had no
  tracked change.
  - Its `rvprobe/` held the review's Lean files, kept here in `probe/` as `*.lean.txt`.
  - It also held copies of the four pre-ship inputs (`NFRouteProbe`, `NFRouteSealControl`,
    `NFImportProbe`, `NDNormalFormOverlay`). These are in the records at
    `campaign/fills/c1/inputs/c1-fill-nf/` and are not duplicated here.
  - Its git dir's `FETCH_HEAD` held the two open PR heads (#175 `ca0eafb8`, #176) fetched for the
    prefix grep (out/05-prefix-grep.txt). No ref was created or moved, and the git dir went with
    the worktree.
- **Kept, not removed.**
  - The `.raw` (unstripped) and `.time` (`/usr/bin/time -l`, exit status) outputs are in `out/`
    beside the path-stripped `.out` files.
  - `out/NFReviewSealControl.v1.*` is the controls' first run, before two control statements were
    corrected. It is the evidence for F14 (an elaboration failure under the `CtlState` seal) and
    for the `summaryEmit s none` remark in section (c).
- **Naming.** The Lean files are named `*.lean.txt` so that the library build never picks them up.
  `scripts/elab.sh` is the live elaboration wrapper; `scripts/elab.sh.txt` is the same file with
  the scratch path replaced by `$S`.
- **`orig/`** holds the draft exactly as reviewed (SHA-256 `783c6ab1…bec8a68`).
