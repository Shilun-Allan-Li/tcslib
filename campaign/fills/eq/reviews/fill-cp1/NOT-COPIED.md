# Not copied from the review folder

Everything under `REVIEW.md`, `NOT-COPIED.md`, `out/` (except `out/aux/`, `out/aux-overlay.txt` and
`out/aux-c1.lean`), `probe/` and `scripts/` is a record. The following are left out; each is a
copy of something already in the records or the inbox, or is derived from them.

- **`delivery/`** (about 5.4 MB): my copies of the inbox's `fill-eq-query.zip` (SHA-256
  `ecad7266…2124`), `fill-eq-query-cp1.zip` (`60d9e7c2…80e4b1`) and `megafill-d-REPORT.md`
  (`caabb14f…858ac`), and the zips' extractions (`scripts/zipextract.py`). The originals stay in
  `exchange/inbox/`, and the session report is already recorded as
  `campaign/fills/megafill/reports/megafill-d-REPORT.md`.
- **`out/aux/`, `out/aux-overlay.txt`, `out/aux-c1.lean`** (about 0.7 MB), each reproducible:
  - `imports-head.json`, `imports-tip.json`: `python3 -I scripts/tools/imports.py <root> <out>`
    on `wt-head` (`9d93626d`) and on the records worktree (`729ffb99`);
  - `screen-base.txt`, `order.txt` and `out/aux-overlay.txt`: the base's
    `campaign/fills/eq/logs/eq-fill-query-screen-base.txt`,
    `campaign/fills/eq/orders/eq-fill-query.txt` and
    `campaign/fills/eq/inputs/eq-fill-query/NTimeDiagonalizerOverlay.lean.txt`;
  - `out/aux-c1.lean`:
    `git show fabce3bb:TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean`;
  - `eq-fill-query.md.<rev>`, `megafill-D.md.<rev>`, `fill-environment-addendum.md.<rev>`: the
    repository copies at `ab09aa41` and `729ffb99` (compared in `out/02-dispatch.txt`);
  - `refgrep-raw.txt` (summarized in `out/22-semantic-greps.txt`), `roots-head.txt` and
    `roots-base.txt` (`scripts/roots.py`; summarized in `out/24`), `tacids.txt` and
    `kinds-ids.txt` (`scripts/tacargs.py`; classified in `out/15`).
- **The review's worktrees** `wt-base`, `wt-head`, `wt-probe`, `wt-am`, `wt-land` and `wt-tip`
  (left in place; `wt-tip` carries the series in its index and E1–E5 in its tree, uncommitted).
  The `.lean` probe copies elaborated in `wt-probe` are the `probe/*.lean.txt` files, renamed.

Lean files are stored as `.lean.txt`. `scripts/tools/` holds copies of the shared tools I ran
(`declfreeze.py` v4 from `devtools/seyoon/`, and `privstmt.py`, `stmtcheck.py`, `codeonly.py`,
`pairdiff.py`, `imports.py`, `leanelab.sh` from the scratchpad's `tools/`), with their
SHA-256s; every elaboration ran through the original `tools/leanelab.sh`.
