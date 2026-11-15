You are filling Ladner fill 6 for the Arora–Barak chapters 3–4 campaign in Shilun-Allan-Li/tcslib: target 5 `Complexity.SAT_mem_P_of_padSAT_NPHard` (the shrinking argument) in `TCSlib/Complexity/Diagonalization/Ladner.lean`.

You are running in a local checkout of the exchange branch `exchange/pass-shelat-ch5-8`. Pull it first (`git pull --rebase`), then read the bundle:

arora-barak-ch3-4/outbox/fills/fill-ladner-shrink/fill-ladner-shrink-bundle.md

SHA-256: 5a2740abb2164fb4339426afd695b5c52cf2e5ebf7629c24468dcf82b2eb46b7
Sections: 13
Lean base: 34643146ee1fe6bf6d7ffdf2e543e8342a3e16a0 (campaign `complexity/arora-barak-ch3-4` after #321)
Records commit: 739faba95499d3e054e7d23a6366328988ca69e5
Exchange commit: e4facafb14e037762b7f5291a403c9c6f6c26b94

Check the SHA-256 first. The first section is the brief, `campaign/fills/ladner-shrink/briefs/ladner-shrink.md`; it is binding, and the other sections are its references. Do the Lean work outside the exchange checkout: fetch the base (`git fetch origin complexity/arora-barak-ch3-4`) and make a separate worktree of `34643146` on a local branch `fill/ladner-shrink`. Never rebase it. Modify only `Ladner.lean`, and put your new section exactly where the brief says: fill 5 (target 2) may be running at the same time on the same file. Follow the bundled fill-environment addendum, bootstrapping the import closure into your own scratch olean tree, and never run `lake build`.

Lean concurrency (binding): this Mac runs other jobs, and at most 3 Lean processes may run at once across the whole machine. Before every Lean launch, count the machine's running Lean processes, matching both a bare `lean` command and a full executable path ending in `/lean` (for example `ps -axo comm= | awk -F/ '$NF=="lean"' | wc -l`). Launch only if the count is below 3. Otherwise wait and recount, and log each wait with a timestamp. Start at most one Lean process of your own at a time, and never run Lean in the background while starting another. If other jobs on the machine share a slot protocol, you may use it, but disclose how in the report.

Delivery: on long runs, push cumulative checkpoint zips `fill-ladner-shrink-checkpoint-N.zip`. At the end, push `fill-ladner-shrink.zip` (REPORT.md per the brief's checklist, the delivered `Ladner.lean`, the patch against `34643146`, the check logs and the concurrency log). Push them to `arora-barak-ch3-4/inbox/fill-ladner-shrink/` on the exchange branch: `git pull --rebase` first, add only that folder, and never force-push. Do not push to any other branch and do not open a pull request. Also attach the final zip in this chat as a fallback. A clean frontier (the arithmetic and the step FP proof done, the loop invariants pending) is a valid delivery; escalate per the brief (E-READER, E-HOST, E-STATEMENT) rather than unfold or invent hosts.
