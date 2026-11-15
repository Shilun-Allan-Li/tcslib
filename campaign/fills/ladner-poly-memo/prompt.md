You are filling Ladner fill 4 for the Arora–Barak chapters 3–4 campaign in Shilun-Allan-Li/tcslib: target 1 part B (the selection scan, the memo driver and readout) and the proof of `Complexity.ladnerH_polyTime` in `TCSlib/Complexity/Diagonalization/Ladner.lean`, after first applying the approved file reorder.

You are running in a local checkout of the exchange branch `exchange/pass-shelat-ch5-8`. Pull it first (`git pull --rebase`), then read the bundle:

arora-barak-ch3-4/outbox/fills/fill-ladner-poly-memo/fill-ladner-poly-memo-bundle.md

SHA-256: cadf4790adac6c7c80431dc6b7e22a30ab5440a9f8713adccd1bf9e148462725
Sections: 15
Lean base: 1320a5c8ce93f4644c2c92ed32e2768ed07ea9bb (campaign `complexity/arora-barak-ch3-4` after #320)
Records commit: 3d7848267a07c3bc3a6144e58b844b795ff83538
Exchange commit: 6e846acb1238f7c365a9e136837d5bf7957c2a79

Check the SHA-256 first. The first section is the brief, `campaign/fills/ladner-poly-memo/briefs/ladner-poly-memo.md`; it is binding, and the other sections are its references. Do the Lean work outside the exchange checkout: fetch the base (`git fetch origin complexity/arora-barak-ch3-4`) and make a separate worktree of `1320a5c8` on a local branch `fill/ladner-poly-memo`. Never rebase it. Step 1 of the brief is a separate commit applying the bundled `Ladner-move.patch.txt` exactly; check the resulting SHA-256 the brief gives. Modify only `Ladner.lean`. Follow the bundled fill-environment addendum, bootstrapping the import closure into your own scratch olean tree, and never run `lake build`.

Lean concurrency (binding): this Mac runs other jobs, and at most 3 Lean processes may run at once across the whole machine. Before every Lean launch, count the machine's running Lean processes, matching both a bare `lean` command and a full executable path ending in `/lean` (for example `ps -axo comm= | awk -F/ '$NF=="lean"' | wc -l`). Launch only if the count is below 3. Otherwise wait and recount, and log each wait with a timestamp. Start at most one Lean process of your own at a time, and never run Lean in the background while starting another. If other jobs on the machine share a slot protocol, you may use it, but disclose how in the report.

Delivery: on long runs, push cumulative checkpoint zips `fill-ladner-poly-memo-checkpoint-N.zip`. At the end, push `fill-ladner-poly-memo.zip` (REPORT.md per the brief's checklist, the delivered `Ladner.lean`, the patch against `1320a5c8` covering both commits, the check logs and the concurrency log). Push them to `arora-barak-ch3-4/inbox/fill-ladner-poly-memo/` on the exchange branch: `git pull --rebase` first, add only that folder, and never force-push. Do not push to any other branch and do not open a pull request. Also attach the final zip in this chat as a fallback. A clean frontier (the reorder plus the selection scan and `stage_correct` done, the memo pending or escalated) is a valid delivery; escalate per the brief (E-READER, E-HOST, E-STATEMENT) rather than unfold or invent hosts.
