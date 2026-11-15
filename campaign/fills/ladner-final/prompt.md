You are filling Ladner fill 7 for the Arora–Barak chapters 3–4 campaign in Shilun-Allan-Li/tcslib: target 6 `Complexity.SAT_H_intermediate`, the last admission in `TCSlib/Complexity/Diagonalization/Ladner.lean`. Proving it completes Ladner's theorem (`Complexity.ladner`).

You are running in a local checkout of the exchange branch `exchange/pass-shelat-ch5-8`. Pull it first (`git pull --rebase`), then read the bundle:

arora-barak-ch3-4/outbox/fills/fill-ladner-final/fill-ladner-final-bundle.md

SHA-256: bc582cf1fbbd8eae6f921b1394976f2f2a8ac763168fbaa10b7a6dfc7b967f09
Sections: 12
Lean base: d811bdaaf5e923b2a57f0453135af5c7ee37713a (campaign `complexity/arora-barak-ch3-4` after #322)
Records commit: 91a58101a87fe27c757584dbfec2924a345432a1
Exchange commit: 37ec3ab5885c8acefcaf1e34e037da9d446f1eff

Check the SHA-256 first. The first section is the brief, `campaign/fills/ladner-final/briefs/ladner-final.md`; it is binding, and the other sections are its references. Do the Lean work outside the exchange checkout: fetch the base (`git fetch origin complexity/arora-barak-ch3-4`) and make a separate worktree of `d811bdaa` on a local branch `fill/ladner-final`. Never rebase it. Modify only `Ladner.lean`. Follow the bundled fill-environment addendum, bootstrapping the import closure into your own scratch olean tree, and never run `lake build`.

Lean concurrency (binding): this Mac runs other jobs, and at most 3 Lean processes may run at once across the whole machine. Before every Lean launch, count the machine's running Lean processes, matching both a bare `lean` command and a full executable path ending in `/lean` (for example `ps -axo comm= | awk -F/ '$NF=="lean"' | wc -l`). Launch only if the count is below 3. Otherwise wait and recount, and log each wait with a timestamp. Start at most one Lean process of your own at a time, and never run Lean in the background while starting another. If other jobs on the machine share a slot protocol, you may use it, but disclose how in the report.

Delivery: on long runs, push cumulative checkpoint zips `fill-ladner-final-checkpoint-N.zip`. At the end, push `fill-ladner-final.zip` (REPORT.md per the brief's checklist, the delivered `Ladner.lean`, the patch against `d811bdaa`, the check logs and the concurrency log). Push them to `arora-barak-ch3-4/inbox/fill-ladner-final/` on the exchange branch: `git pull --rebase` first, add only that folder, and never force-push. Do not push to any other branch and do not open a pull request. Also attach the final zip in this chat as a fallback. A clean frontier (the padding membership and length bound done, the FP construction pending or escalated) is a valid delivery; escalate per the brief (E-READER, E-HOST, E-STATEMENT) rather than unfold or invent hosts.
