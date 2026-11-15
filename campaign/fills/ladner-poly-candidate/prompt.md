You are filling Ladner fill 3 for the Arora–Barak chapters 3–4 campaign in Shilun-Allan-Li/tcslib: target 1 part A, the private declarations of the route's §6 from `values` through `ladner_candidate_FP` (the polynomial-time candidate test) in `TCSlib/Complexity/Diagonalization/Ladner.lean`. This fill proves no Ladner target.

You are running in a local checkout of the exchange branch `exchange/pass-shelat-ch5-8`. Pull it first (`git pull --rebase`), then read the bundle:

arora-barak-ch3-4/outbox/fills/fill-ladner-poly-candidate/fill-ladner-poly-candidate-bundle.md

SHA-256: bbb7206fa72e77f205d167a00e7a052ac3c62b2694a143062afcdc930a5e1876
Sections: 16
Lean base: fe8a8520f65a9feaa4c960c11874b68ebf8798db (campaign `complexity/arora-barak-ch3-4` after #310)
Records commit: d6f7946706984db15349d482e9d04c529d0a38fc
Exchange commit: 88dcdab323199b73c475e0f62a9f7bddff9af6b2

Check the SHA-256 first. The first section is the brief, `campaign/fills/ladner-poly-candidate/briefs/ladner-poly-candidate.md`; it is binding, and the other sections are its references. Do the Lean work outside the exchange checkout: fetch the base (`git fetch origin complexity/arora-barak-ch3-4`) and make a separate worktree of `fe8a8520` on a local branch `fill/ladner-poly-candidate`. Never rebase it. Modify only `Ladner.lean` there. Follow the bundled fill-environment addendum, bootstrapping the import closure into your own scratch olean tree, and never run `lake build`.

Lean concurrency (binding): this Mac runs other jobs, and at most 3 Lean processes may run at once across the whole machine. Before every Lean launch, count the machine's running Lean processes, matching both a bare `lean` command and a full executable path ending in `/lean` (for example `ps -axo comm= | awk -F/ '$NF=="lean"' | wc -l`). Launch only if the count is below 3. Otherwise wait and recount, and log each wait with a timestamp. Start at most one Lean process of your own at a time, and never run Lean in the background while starting another.

Delivery: on long runs, push cumulative checkpoint zips `fill-ladner-poly-candidate-checkpoint-N.zip`. At the end, push `fill-ladner-poly-candidate.zip` (REPORT.md per the brief's checklist, the delivered `Ladner.lean`, the patch against `fe8a8520`, the check logs and the concurrency log). Push them to `arora-barak-ch3-4/inbox/fill-ladner-poly-candidate/` on the exchange branch: `git pull --rebase` first, add only that folder, and never force-push. Do not push to any other branch and do not open a pull request. Also attach the final zip in this chat as a fallback. A clean frontier, with the arithmetic, preparation and simulator leaves complete and the scan escalated or pending, is a valid delivery; escalate per the brief (E-READER, E-HOST, E-STATEMENT) rather than unfold or invent hosts.
